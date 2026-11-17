-- Prove2me | Definitions.Def_LindbladShallow_Supplement_simulator
-- name    : LindbladShallow_Supplement_simulator
-- status  : Definition
-- author  : @iris
-- created : 2026-11-16T14:23:31.139847+00:00
-- url     : https://prove2.me/theorems/ca33684c-1fd9-4a91-a4c1-d2d89ea96a07
-- title:
--   Geometrically local simulators with instruments, adaptive or fixed schedules, and their depth and gate costs (§6.1)
-- statement:
--   A **simulator** of the system of an input acts on the system qubits and on arbitrarily many auxiliary registers, of arbitrary finite dimensions, placed at arbitrary sites of $\mathbb Z^D$. It consists of:
--
--   1. shared input-independent randomness: an arbitrary measurable seed space with a probability measure;
--   2. for each seed, an input-independent initial auxiliary state that is a product over the ambient sites;
--   3. a finite execution bound of $N_{\mathrm{layers}}$ layers of slots; the instruction of each slot (or none) is chosen from the seed and the classical record of the earlier layers.
--
--   An **instruction** is an instrument, in Kraus-density form over an arbitrary measurable classical outcome alphabet, on a set of wires. It is **single-site** when all its wires lie at one site; such instructions (instruments, resets, local randomness) are free. Otherwise it is a **gate**: at most two wires, each of dimension at most $q_g$, at sites at $\ell_\infty$ distance at most $R_g$. The implemented channel is
--   $$
--   \mathcal C(X)=\int_s\int_{\text{branches}}\mathrm{Tr}_{\mathrm{aux}}\bigl[K_b(X\otimes\omega_s)K_b^\dagger\bigr].
--   $$
--
--   The three cost models are:
--   1. **Depth model**: the instructions of a layer act on disjoint wires; each slot has an anchor site, acts within $\ell_\infty$ distance $R_g$ of it, and sees only records of earlier slots whose anchors lie within distance $R_g(t-t')$ (records travel at most $R_g$ sites per layer). The depth is the number of layers.
--   2. **Adaptive schedule**: the cost on an input $\rho$ is the expected number of executed gates, averaged over outcomes and seeds.
--   3. **Fixed schedule**: one deterministic list of gate slots, each on fixed wires, for all branches; other slots may only hold single-site instructions. The cost is the number of gate slots, disabled ones included.
--
--   These are the circuit models in which Theorem 6.1 lower-bounds every simulator.
--
--   **Formalization Note** The seed and outcome alphabets are arbitrary measurable types. Each instruction carries an outcome measure and an operator-valued Kraus density; finite and countable alphabets are the corresponding discrete measures. Outcomes are fine-grained (one Kraus operator each), and a coarse instrument is recovered by having the policy ignore the refinement. One common outcome type loses no generality because instruction-specific alphabets embed in their tagged disjoint union. Explicit integrability conditions exclude only undefined totalized integrals. Gates are arbitrary instruments on their at most two wires. Depth is the number of layers of the execution bound; trailing layers that are idle in every branch can be removed, so this equals depth maximized over branches.
-- source:
--   Shen, Wu, Yuan, Zhang, Shallow Quantum Circuits for Geometrically Local Lindblad Dynamics, arXiv:2610.05362 (held version, sha256 8f4637ef…), §6.1, pp.50–51

import Mathlib
import Definitions.Def_LindbladShallow_Instance
import Definitions.Def_LindbladShallow_dnorm
import Definitions.Def_LindbladShallow_Circuit_channel

open scoped Matrix ComplexOrder
open MeasureTheory

namespace LindbladShallow

namespace Supplement

/-- The ℓ∞ distance `max_i |p_i − q_i|` on `ℤ^D` (arXiv:2610.05362, held version sha256
8f4637ef…, §6.1, p.51: gates "couple sites at ℓ∞ distance at most `R_g`"). -/
def linfDist {D : ℕ} (p q : Fin D → ℤ) : ℕ := Finset.univ.sup fun i => (p i - q i).natAbs

/-- The wires of a simulator of the system of `I` (§6.1, pp.50–51): the system qubits `(j, k)`
(qubit `k` of site `Λ[j]`, dimension 2) and the auxiliary registers `a : A`. -/
abbrev SimWire {P : Params} (I : Instance P) (A : Type) := (Fin I.n × Fin P.d0) ⊕ A

/-- The dimension of a wire: `2` for a system qubit, `dim a` for an auxiliary register. -/
def wireDim {P : Params} {I : Instance P} {A : Type} (dim : A → ℕ) : SimWire I A → ℕ
  | .inl _ => 2
  | .inr a => dim a

/-- The ambient site of a wire: `Λ[j]` for system qubit `(j, k)`, `site a` for an auxiliary
register (an arbitrary point of `ℤ^D`). -/
def wireSite {P : Params} {I : Instance P} {A : Type} (site : A → Site P) : SimWire I A → Site P
  | .inl q => I.sites.get q.1
  | .inr a => site a

/-- A basis configuration of all wires. -/
abbrev SimCfg {P : Params} (I : Instance P) {A : Type} (dim : A → ℕ) :=
  Sys I × ((a : A) → Fin (dim a))

/-- The value of wire `w` in configuration `c`. -/
def cfgVal {P : Params} {I : Instance P} {A : Type} {dim : A → ℕ} (c : SimCfg I dim) :
    (w : SimWire I A) → Fin (wireDim dim w)
  | .inl q => bitIdx (c.1 q)
  | .inr a => c.2 a

/-- A configuration of a finite set of wires. -/
abbrev LocCfg {P : Params} {I : Instance P} {A : Type} [DecidableEq A] (dim : A → ℕ)
    (S : Finset (SimWire I A)) := (w : S) → Fin (wireDim dim w.1)

/-- An instruction of a simulator (§6.1, p.51): an instrument on `wires`, with an arbitrary
measurable classical outcome alphabet. The measure and Kraus density cover finite, countable and
continuous outcomes. -/
structure Instr {P : Params} (I : Instance P) (A : Type) [DecidableEq A] (dim : A → ℕ)
    (O : Type) [MeasurableSpace O] where
  wires : Finset (SimWire I A)
  outcomeMeasure : Measure O
  kraus : O → Matrix (LocCfg dim wires) (LocCfg dim wires) ℂ

variable {P : Params} {I : Instance P} {A : Type} [Fintype A] [DecidableEq A]
  {site : A → Site P} {dim : A → ℕ} {O Seed : Type}
  [MeasurableSpace O] [MeasurableSpace Seed]

/-- Entrywise Bochner integral of a matrix-valued function. -/
noncomputable def matIntegral {X α β : Type} [MeasurableSpace X] (f : X → Matrix α β ℂ)
    (μ : Measure X) : Matrix α β ℂ :=
  Matrix.of fun i j => ∫ x, f x i j ∂μ

/-- Trace preservation for a general-outcome instrument. Integrability is explicit so Lean's
Bochner integral cannot take its default value on a non-integrable Kraus density. -/
def Instr.IsTP (ins : Instr I A dim O) : Prop :=
  (∀ i j, Integrable (fun o => ((ins.kraus o)ᴴ * ins.kraus o) i j) ins.outcomeMeasure) ∧
    matIntegral (fun o => (ins.kraus o)ᴴ * ins.kraus o) ins.outcomeMeasure = 1

/-- Lift of an operator on `S` to all wires, by the identity off `S`. -/
noncomputable def liftInstr (S : Finset (SimWire I A))
    (X : Matrix (LocCfg dim S) (LocCfg dim S) ℂ) : Matrix (SimCfg I dim) (SimCfg I dim) ℂ :=
  open Classical in
  Matrix.of fun c' c => if ∀ w, w ∉ S → cfgVal c' w = cfgVal c w then
    X (fun w => cfgVal c' w.1) (fun w => cfgVal c w.1) else 0

/-- A free single-site instruction. -/
def Instr.IsSingleSite (site : A → Site P) (ins : Instr I A dim O) : Prop :=
  ∀ w ∈ ins.wires, ∀ w' ∈ ins.wires, wireSite (I := I) site w = wireSite site w'

/-- A legal charged gate: at most two wires of dimension at most `q_g`, at sites separated by at
most `R_g` in ℓ∞. -/
def Instr.IsGateOK (site : A → Site P) (qg Rg : ℕ) (ins : Instr I A dim O) : Prop :=
  ins.wires.card ≤ 2 ∧ (∀ w ∈ ins.wires, wireDim dim w ≤ qg) ∧
    ∀ w ∈ ins.wires, ∀ w' ∈ ins.wires,
      linfDist (wireSite (I := I) site w) (wireSite site w') ≤ Rg

/-- Configurations of the auxiliary registers at one ambient site. -/
abbrev AuxAtCfg (site : A → Site P) (dim : A → ℕ) (x : Site P) :=
  (b : {a : A // site a = x}) → Fin (dim b.1)

/-- The product auxiliary state `⨂_x ω_x`, allowing arbitrary correlations within one site. -/
noncomputable def prodAux (site : A → Site P) (dim : A → ℕ)
    (ω : (x : Site P) → Matrix (AuxAtCfg site dim x) (AuxAtCfg site dim x) ℂ) :
    Matrix ((a : A) → Fin (dim a)) ((a : A) → Fin (dim a)) ℂ :=
  open Classical in
  Matrix.of fun a' a => ∏ x ∈ Finset.univ.image site, ω x (fun b => a' b.1) (fun b => a b.1)

/-- `X ⊗ ρ` on system ⊗ auxiliaries. -/
def kronState (X : Matrix (Sys I) (Sys I) ℂ)
    (ρ : Matrix ((a : A) → Fin (dim a)) ((a : A) → Fin (dim a)) ℂ) :
    Matrix (SimCfg I dim) (SimCfg I dim) ℂ :=
  Matrix.of fun c' c => X c'.1 c.1 * ρ c'.2 c.2

/-- A simulator in the models of §6.1. `Seed` and `O` are arbitrary measurable alphabets for
input-independent shared randomness and classical outcomes. A common outcome type loses no
generality, since instruction-specific alphabets embed in their tagged disjoint union. -/
structure Simulator (I : Instance P) (A : Type) [Fintype A] [DecidableEq A] (site : A → Site P)
    (dim : A → ℕ) (Seed O : Type) [MeasurableSpace Seed] [MeasurableSpace O] where
  seedMeasure : Measure Seed
  ω : Seed → (x : Site P) → Matrix (AuxAtCfg site dim x) (AuxAtCfg site dim x) ℂ
  nLayers : ℕ
  nSlots : ℕ
  anchor : ℕ → ℕ → Site P
  policy : Seed → ℕ → ℕ → List (ℕ × ℕ × O) → Option (Instr I A dim O)

namespace Simulator

variable (S : Simulator I A site dim Seed O)

/-- Initial product auxiliary state for a shared-randomness seed. -/
noncomputable def auxState (s : Seed) :
    Matrix ((a : A) → Fin (dim a)) ((a : A) → Fin (dim a)) ℂ :=
  prodAux site dim (S.ω s)

/-- Execute the remaining slots, integrating the branch states over each arbitrary outcome
measure. -/
noncomputable def execFrom :
    ℕ → Seed → ℕ → List (ℕ × ℕ × O) →
      Matrix (SimCfg I dim) (SimCfg I dim) ℂ → Matrix (SimCfg I dim) (SimCfg I dim) ℂ
  | 0, _, _, _, X => X
  | fuel + 1, s, idx, hist, X =>
      let t := idx / S.nSlots
      let j := idx % S.nSlots
      match S.policy s t j hist with
      | none => execFrom fuel s (idx + 1) hist X
      | some ins =>
          matIntegral (fun o => execFrom fuel s (idx + 1) (hist ++ [(t, j, o)])
            (liftInstr ins.wires (ins.kraus o) * X * (liftInstr ins.wires (ins.kraus o))ᴴ))
            ins.outcomeMeasure

/-- Final unnormalized joint state for a fixed seed. -/
noncomputable def runState (s : Seed) (X : Matrix (SimCfg I dim) (SimCfg I dim) ℂ) :
    Matrix (SimCfg I dim) (SimCfg I dim) ℂ :=
  S.execFrom (S.nLayers * S.nSlots) s 0 [] X

/-- Expected future executed-gate count from an unnormalized branch state. -/
noncomputable def costFrom :
    ℕ → Seed → ℕ → List (ℕ × ℕ × O) →
      Matrix (SimCfg I dim) (SimCfg I dim) ℂ → ℝ
  | 0, _, _, _, _ => 0
  | fuel + 1, s, idx, hist, X =>
      let t := idx / S.nSlots
      let j := idx % S.nSlots
      match S.policy s t j hist with
      | none => costFrom fuel s (idx + 1) hist X
      | some ins =>
          ∫ o,
            let X' := liftInstr ins.wires (ins.kraus o) * X *
              (liftInstr ins.wires (ins.kraus o))ᴴ
            letI : Decidable (ins.IsSingleSite site) := Classical.propDecidable _
            costFrom fuel s (idx + 1) (hist ++ [(t, j, o)]) X' +
              if ins.IsSingleSite site then 0 else X'.trace.re
            ∂ins.outcomeMeasure

/-- The implemented system channel, averaged over arbitrary input-independent shared randomness
and all instrument outcomes, with auxiliaries discarded. -/
noncomputable def channel : QAlgorithms.Superop (Sys I) (Sys I) := fun X =>
  matIntegral (fun s => ptrace (S.runState s (kronState X (S.auxState s)))) S.seedMeasure

/-- Expected executed gates on input `ρ`, averaged over outcomes and shared randomness. -/
noncomputable def expGates (ρ : Matrix (Sys I) (Sys I) ℂ) : ℝ :=
  ∫ s, S.costFrom (S.nLayers * S.nSlots) s 0 [] (kronState ρ (S.auxState s)) ∂S.seedMeasure

/-- Validity in every model of §6.1. The integrability clauses are precisely the
measure-theoretic well-formedness conditions for the arbitrary-alphabet execution and prevent
totalized-integral junk values. -/
structure Valid (qg Rg : ℕ) : Prop where
  dim_pos : ∀ a, 1 ≤ dim a
  seed_prob : S.seedMeasure Set.univ = 1
  ω_psd : ∀ s x, (S.ω s x).PosSemidef
  ω_trace : ∀ s x, (S.ω s x).trace = 1
  instr_tp : ∀ s t j h ins, S.policy s t j h = some ins → ins.IsTP
  instr_legal : ∀ s t j h ins, S.policy s t j h = some ins →
    ins.IsSingleSite site ∨ ins.IsGateOK site qg Rg
  exec_integrable : ∀ fuel s (idx : ℕ × ℕ) hist X ins i j,
    S.policy s idx.1 idx.2 hist = some ins →
    Integrable (fun o => (S.execFrom fuel s (idx.1 * S.nSlots + idx.2 + 1)
      (hist ++ [(idx.1, idx.2, o)])
      (liftInstr ins.wires (ins.kraus o) * X * (liftInstr ins.wires (ins.kraus o))ᴴ)) i j)
      ins.outcomeMeasure
  cost_integrable : ∀ fuel s (idx : ℕ × ℕ) hist X ins,
    S.policy s idx.1 idx.2 hist = some ins →
    Integrable (fun o =>
      let X' := liftInstr ins.wires (ins.kraus o) * X *
        (liftInstr ins.wires (ins.kraus o))ᴴ
      letI : Decidable (ins.IsSingleSite site) := Classical.propDecidable _
      S.costFrom fuel s (idx.1 * S.nSlots + idx.2 + 1) (hist ++ [(idx.1, idx.2, o)]) X' +
        if ins.IsSingleSite site then 0 else X'.trace.re) ins.outcomeMeasure
  channel_integrable : ∀ X i j, Integrable
    (fun s => (ptrace (S.runState s (kronState X (S.auxState s)))) i j) S.seedMeasure
  gates_integrable : ∀ ρ, Integrable
    (fun s => S.costFrom (S.nLayers * S.nSlots) s 0 [] (kronState ρ (S.auxState s)))
    S.seedMeasure

/-- The depth model: disjoint layers, local anchors, and classical records propagating at speed
at most `R_g` sites per layer. -/
structure IsDepthModel (Rg : ℕ) : Prop where
  disjoint : ∀ s t h j j' a b, j ≠ j' → S.policy s t j h = some a → S.policy s t j' h = some b →
    Disjoint a.wires b.wires
  near : ∀ s t j h a, S.policy s t j h = some a →
    ∀ w ∈ a.wires, linfDist (wireSite (I := I) site w) (S.anchor t j) ≤ Rg
  causal : ∀ s t j h, S.policy s t j h = S.policy s t j (h.filter fun r =>
    decide (r.1 < t ∧ linfDist (S.anchor r.1 r.2.1) (S.anchor t j) ≤ Rg * (t - r.1)))

/-- A fixed schedule: the same gate-wire set at each charged slot for all seeds and branches. -/
def RespectsSchedule (loc : ℕ → ℕ → Option (Finset (SimWire I A))) : Prop :=
  ∀ s t j h ins, S.policy s t j h = some ins →
    match loc t j with
    | none => ins.IsSingleSite site
    | some W => ins.wires = W

/-- Number of fixed gate slots, disabled slots included. -/
def scheduleCost (loc : ℕ → ℕ → Option (Finset (SimWire I A))) : ℕ :=
  ((Finset.range S.nLayers ×ˢ Finset.range S.nSlots).filter fun p => (loc p.1 p.2).isSome).card

end Simulator

end Supplement

end LindbladShallow



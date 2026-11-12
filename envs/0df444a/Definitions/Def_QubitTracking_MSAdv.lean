-- Prove2me | Definitions.Def_QubitTracking_MSAdv
-- name    : QubitTracking_MSAdv
-- status  : Definition
-- author  : @iris
-- created : 2026-11-11T08:29:33.618354+00:00
-- url     : https://prove2.me/theorems/761b1109-bda9-4646-b697-20c3c86d3122
-- title:
--   The multi-stage monogamy-of-entanglement games (Definitions 6.1, 7.4, 7.8) and black-box extractors
-- statement:
--   In the three multi-stage games the challenger samples $(\mathsf{sk},|\Psi^{\mathsf{sk}}_{n_e,n,n}\rangle)\leftarrow\mathsf{GenAnchorState}$ and gives the vessel to $\mathcal A^0_M$; all parties have the membership oracles $\mathcal O_{T+v}$ and $\mathcal O_{S^\perp+u}$; $\mathcal O^b_C$ outputs $b$ on $C$ and $\bot$ elsewhere. The stage cosets are $C_0=T+v$, $C_1=S^\perp+u$ (Definition 6.1), swapped (Definition 7.4), or $C_{\theta_0}$, $C_{\theta_1}$ for uniform bits (Definition 7.8, with $\theta_0$ given to $\mathcal A^1_M$ and $\theta_1$ to $\mathcal A^2_M$).
--
--   An **adversary** $\mathcal A=(\mathcal A^0_M,\mathcal A^1_M,\mathcal A^2_M,\mathcal A^0_L,\mathcal A^1_L,\mathcal A^0_R,\mathcal A^1_R)$ is a set of qubit wires and seven circuits:
--
--   1. $\mathcal A^0_M$ acts on all wires, may abort (an abort-flag wire), and splits the wires into $\mathbf L,\mathbf M,\mathbf R$;
--   2. $\mathcal A^1_M$ acts on $\mathbf M$ with access to $\mathcal O^{b_0}_{C_0}$ and splits it into $\mathbf M_L,\mathbf M',\mathbf M_R$ (the moment between is BeforeSplit);
--   3. $\mathcal A^0_L$ on $\mathbf L\mathbf M_L$ and $\mathcal A^0_R$ on $\mathbf R\mathbf M_R$ answer $b^l_0$, $b^r_0$;
--   4. $\mathcal A^2_M$ acts on $\mathbf M'$ with $\mathcal O^{b_0}_{C_0}$, $\mathcal O^{b_1}_{C_1}$ and splits it into $\mathbf M'_L,\mathbf M'_R$;
--   5. $\mathcal A^1_L$, $\mathcal A^1_R$ act on what remains of their side with $\mathbf M'_L$, $\mathbf M'_R$ and answer $b^l_1$, $b^r_1$.
--
--   The adversary wins iff $b^l_0=b^r_0=b_0$ and $b^l_1=b^r_1=b_1$. The module defines $\Pr[\neq\bot]$, $\Pr[=1]$, $\varepsilon=1-\Pr[=1]/\Pr[\neq\bot]$, efficient (polynomial-size) families, and the overlap $\mathrm{Tr}(|+\rangle\langle+|_{\mathbf B}|\psi\rangle\langle\psi|)$ of the purified state at BeforeSplit.
--
--   A **black-box extractor** has ancillas holding $\mathsf{sk}$, applies polynomially many ancilla gates and calls of the unitary of $\mathcal A^1_M$ up to BeforeSplit (forward or inverted, possibly controlled), answering its oracle queries with circuits of its own, and outputs an $n$-qubit register $\mathbf X$. The success measures are $\mathbb E[\mathrm{Tr}(\Pi_{\mathrm{eq}}\,\cdot)\mid\text{no abort}]$ for the standard and the Hadamard basis, and the EPR fidelity of the anchor with $\mathbf X$.
--
--   **Formalization Note** Measurements are deferred: answers and the abort flag are read at the end and never touched again. Private ancillas are wires handed over untouched. Purifying $b_0$ in a register $\mathbf B$ (Definition 6.1, step 3) changes nothing because $b_0$ only controls the oracle.
-- source:
--   Bartusek, Huang, Orshansky, Yuen, How To Track Qubits Through Space and Time (Or: Sailing in a Quantum Boat), arXiv:2605.30732 (held version, sha256 bf98e5b5…), Definition 6.1 (pp.32–33), Definition 7.4 (p.52), Definition 7.8 (p.55), Lemma 6.20 (p.48), Lemma 7.1 (pp.49–50), Corollary 7.5 (pp.52–53), Theorem 7.9 (p.55)

import Definitions.Def_QubitTracking_Gate
import Definitions.Def_QubitTracking_anchorVec
import Definitions.Def_PPADSIS_SubexpSIS_Negligible

set_option autoImplicit false

open Matrix

namespace QubitTracking

/-! The multi-stage monogamy-of-entanglement games of Definitions 6.1, 7.4 and 7.8, as one
definition, and black-box extractors.

Source: Bartusek, Huang, Orshansky, Yuen, *How To Track Qubits Through Space and Time (Or:
Sailing in a Quantum Boat)*, arXiv:2605.30732 (held version, sha256 bf98e5b5…), Definition 6.1
(pp.32–33), Definition 7.4 (p.52), Definition 7.8 (p.55), Lemma 7.1 (pp.49–50). -/

/-- The oracles of the multi-stage games: the membership oracles `𝒪_{T+v}`, `𝒪_{S^⊥+u}`
("All parties of the adversary are given oracle access to `𝒪_{T+v}` and `𝒪_{S^⊥+u}`"), and the
stage oracles `𝒪^{b₀}_{C_0}` and `𝒪^{b₁}_{C_1}` (`𝒪^b_C` outputs `b` on inputs in `C` and `⊥`
otherwise, p.26). -/
inductive GOrc : Type
  | memT
  | memS
  | stage0
  | stage1
  deriving DecidableEq

instance : Fintype GOrc where
  elems := {.memT, .memS, .stage0, .stage1}
  complete := by intro x; cases x <;> simp

/-- Every game oracle takes a vector of the vessel space `𝔽₂^d`. -/
abbrev gInLen (d : ℕ) : GOrc → ℕ := fun _ => d

/-- Membership oracles answer one bit; the stage oracles answer an element of `𝔽₂^{m_i} ∪ {⊥}`
in `m_i + 1` qubits. -/
def gOutLen (m0 m1 : ℕ) : GOrc → ℕ
  | .memT => 1
  | .memS => 1
  | .stage0 => m0 + 1
  | .stage1 => m1 + 1

/-- Which of the three games: `search` is Definition 6.1 (`C_0 = T + v`, `C_1 = S^⊥ + u`),
`dual` is Definition 7.4 (`C_0 = S^⊥ + u`, `C_1 = T + v`), `indep` is Definition 7.8 (the stage
cosets `C_{θ₀}`, `C_{θ₁}` for independent uniform bits `θ₀, θ₁`, with `C_0 = T + v`,
`C_1 = S^⊥ + u`). -/
inductive GameMode : Type
  | search
  | dual
  | indep

/-- The stage bases `(θ₀, θ₁)` of a game for sampled bits `(t₀, t₁)`: fixed to `(0, 1)` in
Definition 6.1, `(1, 0)` in Definition 7.4, and the sampled bits in Definition 7.8. -/
def GameMode.thetas : GameMode → ZMod 2 → ZMod 2 → ZMod 2 × ZMod 2
  | .search, _, _ => (0, 1)
  | .dual, _, _ => (1, 0)
  | .indep, t₀, t₁ => (t₀, t₁)

/-- A circuit of the game adversary on wires `W`. -/
abbrev GCirc (W : Type) (d m0 m1 : ℕ) : Type := List (Gate W GOrc (gInLen d) (gOutLen m0 m1))

/-- **An adversary `𝒜 = (𝒜⁰_M, 𝒜¹_M, 𝒜²_M, 𝒜⁰_L, 𝒜¹_L, 𝒜⁰_R, 𝒜¹_R)` of the multi-stage games**
(Definitions 6.1, 7.4, 7.8), on a finite set `W` of qubit wires, all initially `|0⟩` except the
vessel wires `vin`, which receive the vessel register `𝐁` of the anchor state:
* `𝒜⁰_M` runs `g0M` on all wires; the wire `abortW` holds its abort flag (`1` = abort); it hands
  the wire sets `wL`, `wM`, `wR` to `𝒜⁰_L`, `𝒜¹_M`, `𝒜⁰_R`;
* `𝒜¹_M` runs `g1M θ₀` on `wM` (it is given `θ₀` in Definition 7.8) and hands `wML`, `wM'`, `wMR`
  to `𝒜⁰_L`, `𝒜²_M`, `𝒜⁰_R` (the time between is `BeforeSplit`);
* `𝒜⁰_L` runs `g0L` on `wL ∪ wML` and answers `b^l_0` on the wires `b0L`; `𝒜⁰_R` likewise;
* `𝒜²_M` runs `g2M θ₁` on `wM'` and hands `wM'L`, `wM'R` to `𝒜¹_L`, `𝒜¹_R`;
* `𝒜¹_L` runs `g1L` on its remaining wires and `wM'L` and answers `b^l_1` on `b1L`; `𝒜¹_R`
  likewise.

**Formalization Note** Measurements are deferred: answers and the abort flag are read in the
computational basis at the end, and no later party touches them. A party's private ancillas are
wires handed to it untouched. Passing classical data (such as `θ₀`) along is done through the
wires. -/
structure MSAdv (ne n m0 m1 : ℕ) where
  W : Type
  [wFintype : Fintype W]
  [wDecEq : DecidableEq W]
  vin : Fin (n + ne + n) → W
  abortW : W
  wL : Finset W
  wM : Finset W
  wR : Finset W
  wML : Finset W
  wM' : Finset W
  wMR : Finset W
  b0L : Fin m0 → W
  b0R : Fin m0 → W
  wM'L : Finset W
  wM'R : Finset W
  b1L : Fin m1 → W
  b1R : Fin m1 → W
  g0M : GCirc W (n + ne + n) m0 m1
  g1M : ZMod 2 → GCirc W (n + ne + n) m0 m1
  g0L : GCirc W (n + ne + n) m0 m1
  g0R : GCirc W (n + ne + n) m0 m1
  g2M : ZMod 2 → GCirc W (n + ne + n) m0 m1
  g1L : GCirc W (n + ne + n) m0 m1
  g1R : GCirc W (n + ne + n) m0 m1

attribute [instance] MSAdv.wFintype MSAdv.wDecEq

namespace MSAdv

variable {ne n m0 m1 : ℕ}

/-- The wires of `𝒜¹_L`: what `𝒜⁰_L` keeps (`𝐋′`, its register minus its answer wires) together with
`𝐌′_L`. -/
def wL1 (A : MSAdv ne n m0 m1) : Finset A.W :=
  ((A.wL ∪ A.wML) \ Finset.univ.image A.b0L) ∪ A.wM'L

/-- The wires of `𝒜¹_R`. -/
def wR1 (A : MSAdv ne n m0 m1) : Finset A.W :=
  ((A.wR ∪ A.wMR) \ Finset.univ.image A.b0R) ∪ A.wM'R

/-- Every gate of the circuit is well formed and acts only on wires of the set `S`. -/
def CircOn {W : Type} {d : ℕ} (S : Finset W) (gs : GCirc W d m0 m1) : Prop :=
  ∀ g ∈ gs, g.WellFormed ∧ ∀ w, g.Touches w → w ∈ S

/-- The circuit queries only the oracles in `ok`. -/
def CircQueries {W : Type} {d : ℕ} (ok : GOrc → Prop) (gs : GCirc W d m0 m1) : Prop :=
  ∀ g ∈ gs, ∀ o, g.Queries o → ok o

/-- **Validity of a multi-stage adversary for a game mode**: the register hand-offs are disjoint
splits as in Definitions 6.1/7.4/7.8 (steps 2–6); each party acts only on the registers it holds;
the answer wires lie in the answering party's registers; `𝒜⁰_M` queries only the membership
oracles; `𝒜¹_M`, `𝒜⁰_L`, `𝒜⁰_R` do not query the stage-1 oracle (they act before `b₁` exists);
and in Definitions 6.1 and 7.4, where no basis bit is given, `𝒜¹_M` and `𝒜²_M` do not depend on
it. -/
structure Valid (A : MSAdv ne n m0 m1) (mode : GameMode) : Prop where
  vin_inj : Function.Injective A.vin
  abort_out : A.abortW ∉ A.wL ∪ A.wM ∪ A.wR
  split0 : Disjoint A.wL A.wM ∧ Disjoint A.wL A.wR ∧ Disjoint A.wM A.wR
  split1 : A.wML ⊆ A.wM ∧ A.wM' ⊆ A.wM ∧ A.wMR ⊆ A.wM ∧
    Disjoint A.wML A.wM' ∧ Disjoint A.wML A.wMR ∧ Disjoint A.wM' A.wMR
  split2 : A.wM'L ⊆ A.wM' ∧ A.wM'R ⊆ A.wM' ∧ Disjoint A.wM'L A.wM'R
  ans0 : Function.Injective A.b0L ∧ Function.Injective A.b0R ∧
    (∀ j, A.b0L j ∈ A.wL ∪ A.wML) ∧ (∀ j, A.b0R j ∈ A.wR ∪ A.wMR)
  ans1 : Function.Injective A.b1L ∧ Function.Injective A.b1R ∧
    (∀ j, A.b1L j ∈ A.wL1) ∧ (∀ j, A.b1R j ∈ A.wR1)
  c0M : CircOn Finset.univ A.g0M ∧ CircQueries (fun o => o = .memT ∨ o = .memS) A.g0M
  c1M : ∀ θ, CircOn A.wM (A.g1M θ) ∧ CircQueries (fun o => o ≠ .stage1) (A.g1M θ)
  c0L : CircOn (A.wL ∪ A.wML) A.g0L ∧ CircQueries (fun o => o ≠ .stage1) A.g0L
  c0R : CircOn (A.wR ∪ A.wMR) A.g0R ∧ CircQueries (fun o => o ≠ .stage1) A.g0R
  c2M : ∀ θ, CircOn A.wM' (A.g2M θ)
  c1L : CircOn A.wL1 A.g1L
  c1R : CircOn A.wR1 A.g1R
  noTheta : (mode = .search ∨ mode = .dual) → A.g1M 0 = A.g1M 1 ∧ A.g2M 0 = A.g2M 1

/-- The size of the adversary: the total number of gates of its components (the larger branch
for the components given a basis bit). -/
def size (A : MSAdv ne n m0 m1) : ℕ :=
  A.g0M.length + max (A.g1M 0).length (A.g1M 1).length + A.g0L.length + A.g0R.length +
    max (A.g2M 0).length (A.g2M 1).length + A.g1L.length + A.g1R.length

end MSAdv

/-- **Efficient adversary families** for a game mode: valid adversaries whose size is at most
`p(λ)` for a polynomially bounded `p`. -/
def MSEfficient {ne n m0 m1 : ℕ → ℕ} (A : (l : ℕ) → MSAdv (ne l) (n l) (m0 l) (m1 l))
    (mode : GameMode) : Prop :=
  ∃ p : ℕ → ℕ, PPADSIS.SubexpSIS.PolyBounded p ∧ ∀ l, (A l).Valid mode ∧ (A l).size ≤ p l

/-- One sample of the game's randomness: the anchor-state key `(U_shift, u′, v′)` with
`n_h = n_s = n`, the basis bits `(t₀, t₁)` and the stage values `b₀ ∈ 𝔽₂^{m₀}`, `b₁ ∈ 𝔽₂^{m₁}`
(all uniform). -/
abbrev GSample (ne n m0 m1 : ℕ) : Type :=
  GL (Fin (n + ne + n)) (ZMod 2) × Bits (Fin n) × Bits (Fin n) × ZMod 2 × ZMod 2 ×
    Bits (Fin m0) × Bits (Fin m1)

open Classical in
/-- Membership in the stage coset `C_θ`: `C_0 = T + v`, `C_1 = S^⊥ + u` (Definition 7.8, p.55). -/
def cosetMem {ne n : ℕ} (U : GL (Fin (n + ne + n)) (ZMod 2)) (u' v' : Bits (Fin n)) (θ : ZMod 2)
    (z : Bits (Fin (n + ne + n))) : Prop :=
  if θ = 0 then z - anchorV n ne n U v' ∈ anchorT n ne U
  else z - anchorU n ne n U u' ∈ perp (anchorS n U)

open Classical in
/-- The oracles of one sample of the game in mode `mode`: `𝒪_{T+v}`, `𝒪_{S^⊥+u}` (membership,
one bit), `𝒪^{b₀}_{C_{θ₀}}` and `𝒪^{b₁}_{C_{θ₁}}`. -/
noncomputable def gOrc {ne n m0 m1 : ℕ} (mode : GameMode) (ω : GSample ne n m0 m1) :
    OracleAssign GOrc (gInLen (n + ne + n)) (gOutLen m0 m1) :=
  fun o => match o with
    | .memT => fun (z : Bits (Fin (n + ne + n))) => fun _ => if z - anchorV n ne n ω.1 ω.2.2.1 ∈ anchorT n ne ω.1 then 1 else 0
    | .memS => fun (z : Bits (Fin (n + ne + n))) => fun _ =>
        if z - anchorU n ne n ω.1 ω.2.1 ∈ perp (anchorS n ω.1) then 1 else 0
    | .stage0 => fun z =>
        encOpt (if cosetMem ω.1 ω.2.1 ω.2.2.1 (mode.thetas ω.2.2.2.1 ω.2.2.2.2.1).1 z
          then some ω.2.2.2.2.2.1 else none)
    | .stage1 => fun z =>
        encOpt (if cosetMem ω.1 ω.2.1 ω.2.2.1 (mode.thetas ω.2.2.2.1 ω.2.2.2.2.1).2 z
          then some ω.2.2.2.2.2.2 else none)

namespace MSAdv

variable {ne n m0 m1 : ℕ}

/-- The matrix of a circuit of the adversary on the global register `𝐀 ⊗ W` (anchor ⊗ wires). -/
noncomputable def gmat (A : MSAdv ne n m0 m1) (orc : OracleAssign GOrc (gInLen (n + ne + n))
    (gOutLen m0 m1)) (gs : GCirc A.W (n + ne + n) m0 m1) :
    Matrix (Bits (Fin ne ⊕ A.W)) (Bits (Fin ne ⊕ A.W)) ℂ :=
  circMat orc (gs.map (Gate.map Sum.inr))

open Classical in
/-- The initial state: the anchor state `|Ψ^{sk}_{n_e,n,n}⟩` on `𝐀 ⊗ (vessel wires)`, every other
wire `|0⟩` (step 1). -/
noncomputable def init (A : MSAdv ne n m0 m1) (ω : GSample ne n m0 m1) :
    Bits (Fin ne ⊕ A.W) → ℂ :=
  fun f => anchorVec ne n n ω.1 ω.2.1 ω.2.2.1 (fun j => f (Sum.inl j), fun j => f (Sum.inr (A.vin j))) *
    (if ∀ w, (∀ j, A.vin j ≠ w) → f (Sum.inr w) = 0 then 1 else 0)

open Classical in
/-- The (unnormalized) state after `𝒜⁰_M`, projected on "`𝒜⁰_M` does not abort" (abort flag `0`). -/
noncomputable def afterM0 (A : MSAdv ne n m0 m1) (mode : GameMode) (ω : GSample ne n m0 m1) :
    Bits (Fin ne ⊕ A.W) → ℂ :=
  fun f => if f (Sum.inr A.abortW) = 0 then (A.gmat (gOrc mode ω) A.g0M *ᵥ A.init ω) f else 0

/-- The (unnormalized, non-aborting) state at `BeforeSplit`: after `𝒜¹_M`. -/
noncomputable def beforeSplit (A : MSAdv ne n m0 m1) (mode : GameMode) (ω : GSample ne n m0 m1) :
    Bits (Fin ne ⊕ A.W) → ℂ :=
  A.gmat (gOrc mode ω) (A.g1M (mode.thetas ω.2.2.2.1 ω.2.2.2.2.1).1) *ᵥ A.afterM0 mode ω

/-- The (unnormalized, non-aborting) final state, after `𝒜⁰_L`, `𝒜⁰_R`, `𝒜²_M`, `𝒜¹_L`, `𝒜¹_R`. -/
noncomputable def finalSt (A : MSAdv ne n m0 m1) (mode : GameMode) (ω : GSample ne n m0 m1) :
    Bits (Fin ne ⊕ A.W) → ℂ :=
  A.gmat (gOrc mode ω) A.g1R *ᵥ (A.gmat (gOrc mode ω) A.g1L *ᵥ
    (A.gmat (gOrc mode ω) (A.g2M (mode.thetas ω.2.2.2.1 ω.2.2.2.2.1).2) *ᵥ
      (A.gmat (gOrc mode ω) A.g0R *ᵥ (A.gmat (gOrc mode ω) A.g0L *ᵥ A.beforeSplit mode ω))))

/-- `Pr[game(𝒜, 1^λ) ≠ ⊥]`: the probability that `𝒜⁰_M` does not abort. -/
noncomputable def notAbortProb (A : MSAdv ne n m0 m1) (mode : GameMode) : ℝ :=
  avg fun ω : GSample ne n m0 m1 => normSq (A.afterM0 mode ω)

open Classical in
/-- `Pr[game(𝒜, 1^λ) = 1]`: `𝒜⁰_M` does not abort and `b^l_0 = b^r_0 = b₀`, `b^l_1 = b^r_1 = b₁`
(step 6). -/
noncomputable def winProb (A : MSAdv ne n m0 m1) (mode : GameMode) : ℝ :=
  avg fun ω : GSample ne n m0 m1 =>
    ∑ f : Bits (Fin ne ⊕ A.W),
      if (∀ j, f (Sum.inr (A.b0L j)) = ω.2.2.2.2.2.1 j ∧ f (Sum.inr (A.b0R j)) = ω.2.2.2.2.2.1 j) ∧
          (∀ j, f (Sum.inr (A.b1L j)) = ω.2.2.2.2.2.2 j ∧ f (Sum.inr (A.b1R j)) = ω.2.2.2.2.2.2 j)
      then Complex.normSq (A.finalSt mode ω f) else 0

/-- `ε(λ) = 1 − Pr[game = 1]/Pr[game ≠ ⊥]`, the losing probability conditioned on not aborting. -/
noncomputable def lossGivenNotAbort (A : MSAdv ne n m0 m1) (mode : GameMode) : ℝ :=
  1 - A.winProb mode / A.notAbortProb mode

/-- **The `|+⟩_𝐁` overlap at `BeforeSplit`** (Lemma 6.20, p.48), in Definition 6.1's game: with the
stage-0 value `b₀` purified in a register `𝐁` initialized to `|+⟩` and `sk` purified in a register
`🔑`, the state at `BeforeSplit` conditioned on `𝒜⁰_M` not aborting is
`|ψ⟩ ∝ ∑_{sk} √Pr[sk] |sk⟩ ∑_{b₀} 2^{-m₀/2} |φ_{sk,b₀}⟩|b₀⟩_𝐁`, and
`Tr(|+⟩⟨+|_𝐁 |ψ⟩⟨ψ|) = 𝔼_{sk} ‖2^{-m₀} ∑_{b₀} φ_{sk,b₀}‖² / Pr[≠ ⊥]`, with `φ_{sk,b₀}` the
(unnormalized, non-aborting) state at `BeforeSplit` for stage-0 value `b₀`.

**Formalization Note** `b₀` enters only as the value returned by the stage-0 oracle, so the
purified `𝐁` register acts only as a control; this is the formula for the purified state. -/
noncomputable def plusOverlap (A : MSAdv ne n m0 m1) : ℝ :=
  (avg fun ω : GSample ne n m0 m1 =>
      normSq fun f => ((2 : ℂ) ^ m0)⁻¹ * ∑ b : Bits (Fin m0),
        A.beforeSplit .search (ω.1, ω.2.1, ω.2.2.1, ω.2.2.2.1, ω.2.2.2.2.1, b, ω.2.2.2.2.2.2) f) /
    A.notAbortProb .search

end MSAdv

/-- One step of a black-box extractor with `k` ancilla qubits: a one- or two-qubit gate on the
ancillas (no oracle), or a call to the black box `𝒜¹_M` (run up to `BeforeSplit`) with basis input
`θ`, forward or inverted (`inv`), possibly controlled on an ancilla. -/
inductive ExtStep (k : ℕ) : Type
  | gate (g : Gate (Fin k) Empty Empty.elim Empty.elim)
  | call (θ : ZMod 2) (inv : Bool) (ctrl : Option (Fin k))

/-- **An efficient extractor with access to `sk` and the register `𝐌`, making black-box access to
`𝒜¹_M`** (Lemma 7.1, p.50; Corollary 7.5, p.53; Theorem 7.9, p.55), with `k` ancilla qubits:
* the secret key `sk = (U_shift, u, v)` (p.27) is written in the computational basis on the
  ancillas `skW`, every other ancilla starts in `|0⟩`;
* `impl o` is the circuit by which the extractor answers the black box's queries to oracle `o`:
  it acts on the query's input and output wires and on the ancillas;
* `prog` is the program: ancilla gates and black-box calls;
* `out` is the output register `𝐗` (`n` qubits).

**Formalization Note** "Black-box access to `𝒜¹_M`" is read as: the extractor runs the unitary of
`𝒜¹_M` up to `BeforeSplit` (forward or inverted, possibly controlled), answering its oracle queries
with oracles of its own choosing, and otherwise acts only on its ancillas; this is how the
extractors of Lemma 7.1 (compressed-oracle simulation), Corollary 7.5 and Theorem 7.9 (controlled
`ℰ_S`, `ℰ_H` and their reverses, through Corollary 7.7) are built. -/
structure BBExt (ne n m0 m1 nOut : ℕ) where
  k : ℕ
  skW : (Fin (n + ne + n) × Fin (n + ne + n)) ⊕ Fin (n + ne + n) ⊕ Fin (n + ne + n) → Fin k
  out : Fin nOut → Fin k
  impl : (o : GOrc) →
    List (Gate (Fin (gInLen (n + ne + n) o) ⊕ Fin (gOutLen m0 m1 o) ⊕ Fin k) Empty Empty.elim
      Empty.elim)
  prog : List (ExtStep k)

namespace BBExt

variable {ne n m0 m1 nOut : ℕ}

/-- Validity: the `sk` wires and the output wires are injective, every gate is well formed, and a
call's control ancilla is never touched by the query-answering circuits. -/
structure Valid (E : BBExt ne n m0 m1 nOut) : Prop where
  skW_inj : Function.Injective E.skW
  out_inj : Function.Injective E.out
  impl_wf : ∀ o, ∀ g ∈ E.impl o, g.WellFormed
  prog_wf : ∀ g, ExtStep.gate g ∈ E.prog → g.WellFormed
  ctrl_free : ∀ θ inv c, ExtStep.call θ inv (some c) ∈ E.prog →
    ∀ o, ∀ g ∈ E.impl o, ¬ g.Touches (Sum.inr (Sum.inr c))

/-- The cost of the extractor: the number of program steps (each black-box call counts once) plus
the sizes of the query-answering circuits. -/
def cost (E : BBExt ne n m0 m1 nOut) : ℕ :=
  E.prog.length + ∑ o : GOrc, (E.impl o).length

end BBExt

/-- **Efficient extractor families**: valid extractors of cost at most `p(λ)`, `p` polynomially
bounded. -/
def BBEfficient {ne n m0 m1 nOut : ℕ → ℕ}
    (E : (l : ℕ) → BBExt (ne l) (n l) (m0 l) (m1 l) (nOut l)) : Prop :=
  ∃ p : ℕ → ℕ, PPADSIS.SubexpSIS.PolyBounded p ∧ ∀ l, (E l).Valid ∧ (E l).cost ≤ p l

namespace BBExt

variable {ne n m0 m1 nOut : ℕ}

/-- The global wires of the extraction: anchor `𝐀`, the adversary's wires `W`, the ancillas. -/
abbrev XW (E : BBExt ne n m0 m1 nOut) (A : MSAdv ne n m0 m1) : Type :=
  (Fin ne ⊕ A.W) ⊕ Fin E.k

/-- The gates of one forward black-box run of `𝒜¹_M(θ)` on the global wires, its queries answered
by the extractor's circuits `impl`. -/
def substCirc (E : BBExt ne n m0 m1 nOut) (A : MSAdv ne n m0 m1) (θ : ZMod 2) :
    List (Gate (E.XW A) Empty Empty.elim Empty.elim) :=
  (A.g1M θ).flatMap fun g => match g with
    | .one c U => [.one (Sum.inl (Sum.inr c)) U]
    | .two c₁ c₂ U => [.two (Sum.inl (Sum.inr c₁)) (Sum.inl (Sum.inr c₂)) U]
    | .query o inp out =>
        (E.impl o).map (Gate.map
          (Sum.elim (fun j => Sum.inl (Sum.inr (inp j)))
            (Sum.elim (fun j => Sum.inl (Sum.inr (out j))) Sum.inr)))

open Classical in
/-- The matrix of one program step on the global wires. A controlled call `M` becomes
`P₀ + P₁ M P₁`, `P_b` the projector on "control ancilla `= b`"; an inverted call is `M†`. -/
noncomputable def stepMat (E : BBExt ne n m0 m1 nOut) (A : MSAdv ne n m0 m1) :
    ExtStep E.k → Matrix (Bits (E.XW A)) (Bits (E.XW A)) ℂ
  | .gate g => (g.map Sum.inr).mat (fun e => e.elim)
  | .call θ inv ctrl =>
      let V := circMat (fun e => e.elim) (E.substCirc A θ)
      let M := if inv then Vᴴ else V
      match ctrl with
      | none => M
      | some c =>
          let P : ZMod 2 → Matrix (Bits (E.XW A)) (Bits (E.XW A)) ℂ :=
            fun b => Matrix.diagonal fun f => if f (Sum.inr c) = b then 1 else 0
          P 0 + P 1 * M * P 1

/-- The matrix of the whole program. -/
noncomputable def progMat (E : BBExt ne n m0 m1 nOut) (A : MSAdv ne n m0 m1) :
    Matrix (Bits (E.XW A)) (Bits (E.XW A)) ℂ :=
  E.prog.foldl (fun acc s => E.stepMat A s * acc) 1

open Classical in
/-- The bits of `sk = (U_shift, u, v)` (p.27). -/
noncomputable def skVal {ne n m0 m1 : ℕ} (ω : GSample ne n m0 m1) :
    (Fin (n + ne + n) × Fin (n + ne + n)) ⊕ Fin (n + ne + n) ⊕ Fin (n + ne + n) → ZMod 2 :=
  Sum.elim (fun ij => (ω.1 : Matrix (Fin (n + ne + n)) (Fin (n + ne + n)) (ZMod 2)) ij.1 ij.2)
    (Sum.elim (anchorU n ne n ω.1 ω.2.1) (anchorV n ne n ω.1 ω.2.2.1))

open Classical in
/-- **The extractor's output state** on a sample: run the program on the non-aborting state
after `𝒜⁰_M` (on `𝐀 ⊗ W`) tensored with the ancillas (holding `sk`). -/
noncomputable def output (E : BBExt ne n m0 m1 nOut) (A : MSAdv ne n m0 m1) (mode : GameMode)
    (ω : GSample ne n m0 m1) : Bits (E.XW A) → ℂ :=
  E.progMat A *ᵥ fun f =>
    A.afterM0 mode ω (fun w => f (Sum.inl w)) *
      (if (∀ j, f (Sum.inr (E.skW j)) = skVal ω j) ∧
          (∀ a, (∀ j, E.skW j ≠ a) → f (Sum.inr a) = 0)
        then 1 else 0)

open Classical in
/-- **Extraction of the standard-basis value of the anchor** (Lemma 7.1, p.50): the conditional
success probability
`𝔼[Tr(Π_eq ℰ ρ_𝐌 ℰ† Π_eq) | 𝒜⁰_M does not abort]`, `Π_eq = ∑_x |x⟩⟨x|_𝐀 ⊗ |x⟩⟨x|_𝐗`: the averaged
probability that the output register equals the anchor in the computational basis, divided by
`Pr[≠ ⊥]`. -/
noncomputable def stdSucc (E : BBExt n n m0 m1 n) (A : MSAdv n n m0 m1) (mode : GameMode) : ℝ :=
  (avg fun ω : GSample n n m0 m1 =>
      ∑ f : Bits (E.XW A),
        if ∀ i, f (Sum.inl (Sum.inl i)) = f (Sum.inr (E.out i))
        then Complex.normSq (E.output A mode ω f) else 0) / A.notAbortProb mode

open Classical in
/-- **Extraction of the Hadamard-basis value of the anchor** (Corollary 7.5, p.53): as `stdSucc`
with `Π_eq = ∑_x H^{⊗n}|x⟩⟨x|H^{⊗n} ⊗ |x⟩⟨x|_𝐗`, i.e. after applying `H^{⊗n}` to the anchor. -/
noncomputable def hadSucc (E : BBExt n n m0 m1 n) (A : MSAdv n n m0 m1) (mode : GameMode) : ℝ :=
  (avg fun ω : GSample n n m0 m1 =>
      ∑ f : Bits (E.XW A),
        if ∀ i, f (Sum.inl (Sum.inl i)) = f (Sum.inr (E.out i))
        then Complex.normSq
          ((onWires (fun i : Fin n => (Sum.inl (Sum.inl i) : E.XW A)) (hadamard (Fin n)) *ᵥ
            E.output A mode ω) f)
        else 0) / A.notAbortProb mode

/-- The vector `|EPR⟩^{⊗n}` on `2n` qubits indexed by `Fin (n + n)`, qubit `i` paired with qubit
`n + i`. -/
noncomputable def eprBits (n : ℕ) : Bits (Fin (n + n)) → ℂ :=
  fun b => if ∀ i : Fin n, b (Fin.castAdd n i) = b (Fin.natAdd n i)
    then ((Real.sqrt 2 : ℂ) ^ n)⁻¹ else 0

/-- **EPR fidelity of the extracted register** (Theorem 7.9, p.55):
`𝔼[Tr(⟨EPR|^{⊗n}_{𝐀𝐗} ℰ ρ_𝐌 ℰ† |EPR⟩^{⊗n}_{𝐀𝐗}) | 𝒜⁰_M does not abort]`, the `j`-th anchor qubit paired
with the `j`-th output qubit. -/
noncomputable def eprSucc (E : BBExt n n m0 m1 n) (A : MSAdv n n m0 m1) (mode : GameMode) : ℝ :=
  (avg fun ω : GSample n n m0 m1 =>
      (inner' (E.output A mode ω)
        (onWires (Fin.append (fun i : Fin n => (Sum.inl (Sum.inl i) : E.XW A))
            (fun i : Fin n => (Sum.inr (E.out i) : E.XW A))) (proj (eprBits n)) *ᵥ
          E.output A mode ω)).re) / A.notAbortProb mode

end BBExt

end QubitTracking



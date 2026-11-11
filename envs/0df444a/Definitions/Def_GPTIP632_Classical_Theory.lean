-- Prove2me | Definitions.Def_GPTIP632_Classical_Theory
-- name    : GPTIP632_Classical_Theory
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-10T21:02:04.267619+00:00
-- url     : https://prove2.me/theorems/47ac38c6-2c99-4fb7-9fd9-034f959b6683
-- title:
--   Theories: channels and instruments positive on all extensions, Definition B.16, and the standing assumptions (T1)–(T4)
-- statement:
--   A **theory** $\mathcal G$ consists of a collection $S_{\mathcal G}$ of systems (in coordinates), closed under a composite operation $(A,B)\mapsto AB$ whose coordinates are pairs of coordinates, a finite set of **elementary** systems, the designated **standard classical systems** $\Delta_{n}$ ($n\ge1$; $\Delta_1$ is the trivial system $I$), and, for systems $A$, $B$, sets of **allowed channels** and **allowed instruments** from $A$ to $B$, given as real matrices in coordinates.
--
--   A linear map $\Phi:V_A\to V_B$ is **positive on all extensions** if $\Phi(V_A^+)\subseteq V_B^+$ and $(\Phi\otimes\mathrm{id}_C)(V_{AC}^+)\subseteq V_{BC}^+$ for every system $C$ of the theory. A **channel** is such a map with $u_B\circ\Phi=u_A$; an **instrument** with outcomes $\{1,\dots,k\}$ is a family of maps positive on all extensions whose sum is a channel (Definition B.11).
--
--   The axioms (Definition B.6 with (T1)–(T2), and Definition B.16) are:
--
--   1. composites satisfy $u_{AB}=u_A\otimes u_B$ and $V_A^+\otimes_{\min}V_B^+\subseteq V_{AB}^+\subseteq V_A^+\otimes_{\max}V_B^+$;
--   2. composition is associative and symmetric up to the re-indexing of coordinates, the cones corresponding;
--   3. each $\Delta_n$ has the orthant cone and the all-ones unit in its coordinates;
--   4. allowed channels and instruments satisfy Definition B.11;
--   5. they are closed under sequential and parallel composition, contain the identity channels, the discards $u_A$ and the preparations of all states of all systems; outcomes may be coarse-grained; every allowed instrument $(\Phi_i)_i$ has the allowed flagged channel $\omega\mapsto\sum_i\delta_i\otimes\Phi_i(\omega)$.
--
--   A theory comes with a **finite gate set**: allowed instruments acting on composites of elementary systems. The **standing assumptions** add:
--
--   - **(T3)** every stochastic map between classical systems (the $\Delta_n$ and their composites) is an allowed channel; the readout of $\Delta_n$ is allowed; classical control $\delta_i\otimes\alpha\mapsto\delta_i\otimes\Phi_i(\alpha)$ of allowed channels and of allowed instruments is allowed;
--   - **(T4)** every matrix entry of every gate outcome map and every coordinate of every elementary unit effect is approximable within $2^{-k}$ in time $\mathrm{poly}(k)$; the gate set contains a fixed preparation and the discard of each elementary system and, on the classical bit $\Delta_2$ as an elementary system, its readout, a fair coin, the preparation of $\delta_0$, NOT and Toffoli.
--
--   This is the class of theories over which Theorem 1.1 quantifies.
--
--   **Formalization Note** `Core` holds the data, `Core.IsTheory` the axioms, and `Theory` adds the gate set (with each gate an allowed instrument). `Theory.Standing` is (T3) ∧ (T4). Wires of a register are lists of elementary systems with coordinates `coords`; `gk` reads a gate as a kernel on such coordinates. In (T4), "a universal set of classical reversible gates" is read as NOT and Toffoli together with the constant $\delta_0$ on an elementary classical bit; "classical systems" in (T3) are the composites of the designated $\Delta_n$. Polynomial time means an `OTM` clocked by a polynomial and run with the empty oracle; rationals are written by `encRat`.
--
--   The composition axioms require closure separately for channels and for instruments; mixed channel/instrument compositions are not required. This admits a larger class of structures than Definition B.16, and every source theory satisfies these axioms.
-- source:
--   Kishor Bharti, Beyond IP = PSPACE and QIP = PSPACE: Interactive Proofs in Arbitrary Physical Theories, STOC 2027 submission #632 (October 2026), source.pdf SHA-256 ebbc45027e7a3b48cbfb1a2deb89e9a7d8374373b23763680b948fda16cf4da7, pp.15–17 (PDF pp.17–19), Definition B.6, Definition B.11, Definition B.16, (T1)–(T4); p.20 (PDF p.22), §C

import Mathlib
import Definitions.Def_GPTIP632_Classical_Systems
import Definitions.Def_QAdvFew_PoQOracle_OTM
import Definitions.Def_QAdvFew_PoQOracle_tup

/-!
# Theories, their channels and instruments, and the standing assumptions (T1)–(T4)

Kishor Bharti, *Beyond IP = PSPACE and QIP = PSPACE: Interactive Proofs in Arbitrary Physical
Theories*, STOC 2027 submission #632 (October 2026), Definition B.6 (p.15, PDF p.17),
Definition B.11 (p.16, PDF p.18), Definition B.16 and (T1)–(T4) (p.17, PDF p.19), §C (p.20,
PDF p.22).

The systems of a theory form a type `Sys`; every system carries coordinates, and the composite
`comp A B` comes with an identification of its coordinates with `ι_A × ι_B` (local tomography,
(T1)). Linear maps `V_A → V_B` are real matrices indexed by `ι_B × ι_A`.
-/

namespace GPTIP632.Classical

open QAlgorithms.Complexity QAdvFew.PoQOracle

/-- The data of a theory (Definition B.16, p.17): (a) a collection `Sys` of systems, closed under
composites `comp`, with a finite type `Elem` of elementary systems and the designated standard
classical systems `cl n = Δ_{n+1}` of (T3); (b) for each pair of systems the allowed channels
`chan A B` and, for each number `k` of outcomes, the allowed instruments `inst A B k`. The axioms
are in `Core.IsTheory`. -/
structure Core where
  /-- the collection `S_G` of systems -/
  Sys : Type
  /-- the system (coordinates, cone, unit) of each member of `S_G` -/
  sys : Sys → System
  /-- the composite `AB` of `A` and `B` -/
  comp : Sys → Sys → Sys
  /-- local tomography (T1): the coordinates of `AB` are pairs of coordinates -/
  compEquiv : ∀ A B : Sys, (sys (comp A B)).ι ≃ (sys A).ι × (sys B).ι
  /-- the finite set of elementary systems -/
  Elem : Type
  [elemFintype : Fintype Elem]
  [elemDecEq : DecidableEq Elem]
  elem : Elem → Sys
  /-- the designated standard classical system `Δ_{n+1}` -/
  cl : ℕ → Sys
  /-- its coordinates are labelled `1, …, n+1` (here `Fin (n+1)`) -/
  clEquiv : ∀ n, (sys (cl n)).ι ≃ Fin (n + 1)
  /-- allowed channels `Chan_G(A, B)` -/
  chan : (A B : Sys) → Set (Matrix (sys B).ι (sys A).ι ℝ)
  /-- allowed instruments from `A` to `B` with outcomes `Fin k` -/
  inst : (A B : Sys) → (k : ℕ) → Set (Fin k → Matrix (sys B).ι (sys A).ι ℝ)

attribute [instance] Core.elemFintype Core.elemDecEq

namespace Core

variable (C : Core)

/-- The trivial system `I = Δ_1` (`V = ℝ`, `V⁺ = ℝ_{≥0}`, `u = id`). -/
abbrev triv : C.Sys := C.cl 0

/-- The register of a list of elementary wires: `[] ↦ I`, `[a] ↦ a`, `a :: l ↦ a (reg l)`. -/
def reg : List C.Elem → C.Sys
  | [] => C.cl 0
  | [a] => C.elem a
  | a :: b :: l => C.comp (C.elem a) (reg (b :: l))

/-- `Φ ⊗ id_D` as a matrix on the coordinates of the composites `AD → BD`. -/
def tensorId {A B : C.Sys} (Φ : Matrix (C.sys B).ι (C.sys A).ι ℝ) (D : C.Sys) :
    Matrix (C.sys (C.comp B D)).ι (C.sys (C.comp A D)).ι ℝ :=
  fun k l => Φ (C.compEquiv B D k).1 (C.compEquiv A D l).1 *
    if (C.compEquiv B D k).2 = (C.compEquiv A D l).2 then 1 else 0

/-- Parallel composition `Φ ⊗ Ψ : AD → BE` in product coordinates. -/
def parMat {A B D E : C.Sys} (Φ : Matrix (C.sys B).ι (C.sys A).ι ℝ)
    (Ψ : Matrix (C.sys E).ι (C.sys D).ι ℝ) : Matrix (C.sys (C.comp B E)).ι (C.sys (C.comp A D)).ι ℝ :=
  fun k l => Φ (C.compEquiv B E k).1 (C.compEquiv A D l).1 * Ψ (C.compEquiv B E k).2 (C.compEquiv A D l).2

/-- **Definition B.11**, p.16: `Φ : V_A → V_B` is *positive on all extensions* if `Φ ⊗ id_D` maps
`V_{AD}⁺` into `V_{BD}⁺` for every system `D` of the theory, and for `D = I` (the first clause:
`Φ(V_A⁺) ⊆ V_B⁺`). -/
def PosAllExt {A B : C.Sys} (Φ : Matrix (C.sys B).ι (C.sys A).ι ℝ) : Prop :=
  (∀ ω ∈ (C.sys A).cone, Φ.mulVec ω ∈ (C.sys B).cone) ∧
  ∀ D : C.Sys, ∀ ξ ∈ (C.sys (C.comp A D)).cone, (C.tensorId Φ D).mulVec ξ ∈ (C.sys (C.comp B D)).cone

/-- **Definition B.11**: a *channel* is a map positive on all extensions with `u_B ∘ Φ = u_A`. -/
def IsChannel {A B : C.Sys} (Φ : Matrix (C.sys B).ι (C.sys A).ι ℝ) : Prop :=
  C.PosAllExt Φ ∧ Matrix.vecMul (C.sys B).unit Φ = (C.sys A).unit

/-- **Definition B.11**: an *instrument* with outcomes `Fin k` is a family of maps positive on all
extensions whose sum is a channel. -/
def IsInstrument {A B : C.Sys} {k : ℕ} (Φ : Fin k → Matrix (C.sys B).ι (C.sys A).ι ℝ) : Prop :=
  (∀ o, C.PosAllExt (Φ o)) ∧ C.IsChannel (∑ o, Φ o)

/-- The coordinates of `(AB)D`, identified with `(ι_A × ι_B) × ι_D`. -/
def e3L (A B D : C.Sys) : (C.sys (C.comp (C.comp A B) D)).ι ≃ ((C.sys A).ι × (C.sys B).ι) × (C.sys D).ι :=
  (C.compEquiv _ _).trans (Equiv.prodCongr (C.compEquiv A B) (Equiv.refl _))

/-- The coordinates of `A(BD)`, identified with `ι_A × (ι_B × ι_D)`. -/
def e3R (A B D : C.Sys) : (C.sys (C.comp A (C.comp B D))).ι ≃ (C.sys A).ι × ((C.sys B).ι × (C.sys D).ι) :=
  (C.compEquiv _ _).trans (Equiv.prodCongr (Equiv.refl _) (C.compEquiv B D))

/-- The flagged channel `ω ↦ ∑_i δ_i ⊗ Φ_i(ω)` of an instrument with outcomes `Fin (k+1)`,
recording the outcome in the classical register `Δ_{k+1}`. -/
def flagMat {A B : C.Sys} {k : ℕ} (Φ : Fin (k + 1) → Matrix (C.sys B).ι (C.sys A).ι ℝ) :
    Matrix (C.sys (C.comp (C.cl k) B)).ι (C.sys A).ι ℝ :=
  fun p l => Φ (C.clEquiv k (C.compEquiv _ _ p).1) (C.compEquiv _ _ p).2 l

/-- **Definition B.6 with (T1)–(T2) and Definition B.16** (pp.15–17): the axioms of a theory.

1. Composites (Definition B.6, (T1)): `u_AB = u_A ⊗ u_B` and
   `V_A⁺ ⊗_min V_B⁺ ⊆ V_AB⁺ ⊆ V_A⁺ ⊗_max V_B⁺` in product coordinates.
2. Composition is associative and symmetric up to the obvious re-indexings: the cones correspond.
3. The designated `Δ_{n+1}` are the standard classical systems of Example B.2.
4. Allowed channels and instruments satisfy Definition B.11 (this contains (T2)).
5. Allowed operations are closed under sequential and parallel composition, contain the identity
   channels, the discards `u_A` and the preparations of all states of all systems; outcomes of
   instruments may be coarse-grained; every allowed instrument has an allowed flagged channel. -/
structure IsTheory : Prop where
  comp_unit : ∀ A B k, (C.sys (C.comp A B)).unit k =
    (C.sys A).unit (C.compEquiv A B k).1 * (C.sys B).unit (C.compEquiv A B k).2
  comp_min : ∀ A B, minTensor (C.sys A) (C.sys B) ⊆ pullCone (C.sys (C.comp A B)) (C.compEquiv A B)
  comp_max : ∀ A B, pullCone (C.sys (C.comp A B)) (C.compEquiv A B) ⊆ maxTensor (C.sys A) (C.sys B)
  comp_assoc : ∀ A B D (ξ : ((C.sys A).ι × (C.sys B).ι) × (C.sys D).ι → ℝ),
    ξ ∈ pullCone _ (C.e3L A B D) ↔ (ξ ∘ (Equiv.prodAssoc _ _ _).symm) ∈ pullCone _ (C.e3R A B D)
  comp_symm : ∀ A B (ξ : (C.sys A).ι × (C.sys B).ι → ℝ),
    ξ ∈ pullCone _ (C.compEquiv A B) ↔ (ξ ∘ Prod.swap) ∈ pullCone _ (C.compEquiv B A)
  cl_cone : ∀ n (ω : (C.sys (C.cl n)).ι → ℝ), ω ∈ (C.sys (C.cl n)).cone ↔ ∀ k, 0 ≤ ω k
  cl_unit : ∀ n k, (C.sys (C.cl n)).unit k = 1
  chan_ok : ∀ A B, ∀ Φ ∈ C.chan A B, C.IsChannel Φ
  inst_ok : ∀ A B k, ∀ Φ ∈ C.inst A B k, C.IsInstrument Φ
  chan_seq : ∀ A B D, ∀ Φ ∈ C.chan A B, ∀ Ψ ∈ C.chan B D, Ψ * Φ ∈ C.chan A D
  chan_par : ∀ A B D E, ∀ Φ ∈ C.chan A B, ∀ Ψ ∈ C.chan D E, C.parMat Φ Ψ ∈ C.chan (C.comp A D) (C.comp B E)
  inst_seq : ∀ A B D k m, ∀ Φ ∈ C.inst A B k, ∀ Ψ ∈ C.inst B D m,
    (fun o : Fin (k * m) => Ψ (finProdFinEquiv.symm o).2 * Φ (finProdFinEquiv.symm o).1) ∈ C.inst A D (k * m)
  inst_par : ∀ A B D E k m, ∀ Φ ∈ C.inst A B k, ∀ Ψ ∈ C.inst D E m,
    (fun o : Fin (k * m) => C.parMat (Φ (finProdFinEquiv.symm o).1) (Ψ (finProdFinEquiv.symm o).2)) ∈
      C.inst (C.comp A D) (C.comp B E) (k * m)
  chan_id : ∀ A, (1 : Matrix (C.sys A).ι (C.sys A).ι ℝ) ∈ C.chan A A
  chan_discard : ∀ A, (fun _ j => (C.sys A).unit j : Matrix (C.sys C.triv).ι (C.sys A).ι ℝ) ∈ C.chan A C.triv
  chan_prep : ∀ A, ∀ ω ∈ (C.sys A).states,
    (fun i _ => ω i : Matrix (C.sys A).ι (C.sys C.triv).ι ℝ) ∈ C.chan C.triv A
  inst_coarse : ∀ A B k m, ∀ Φ ∈ C.inst A B k, ∀ c : Fin k → Fin m,
    (fun j => ∑ i ∈ Finset.univ.filter (fun i => c i = j), Φ i) ∈ C.inst A B m
  inst_flag : ∀ A B k, ∀ Φ ∈ C.inst A B (k + 1), C.flagMat Φ ∈ C.chan A (C.comp (C.cl k) B)

/-! ### Wires and raw coordinates -/

/-- A wire coordinate: an elementary system together with one of its coordinate labels. A
coordinate of a register `l` is a list of wire coordinates whose systems read `l`. -/
abbrev Wire := Σ a : C.Elem, (C.sys (C.elem a)).ι

/-- The coordinate of the elementary system `a` carried by a wire coordinate, if it is of type `a`. -/
def wireIdx (a : C.Elem) (w : C.Wire) : Option (C.sys (C.elem a)).ι :=
  if h : w.1 = a then some (h ▸ w.2) else none

/-- Decode a list of wire coordinates as a coordinate of the register `reg l` (through the
coordinate identifications of the composites); `none` if the list does not have the types `l`. -/
def regIdx : (l : List C.Elem) → List C.Wire → Option (C.sys (C.reg l)).ι
  | [], [] => some ((C.clEquiv 0).symm 0)
  | [a], [w] => C.wireIdx a w
  | a :: b :: l, w :: k =>
      match C.wireIdx a w, regIdx (b :: l) k with
      | some i, some j => some ((C.compEquiv _ _).symm (i, j))
      | _, _ => none
  | _, _ => none

/-- The coordinate labels of the register `l`: all lists of wire coordinates with types `l`. -/
def coords : List C.Elem → Finset (List C.Wire)
  | [] => {[]}
  | a :: l => ((Finset.univ : Finset (C.sys (C.elem a)).ι) ×ˢ coords l).image
      (fun p => (⟨a, p.1⟩ : C.Wire) :: p.2)

/-- The unit effect of a register at a coordinate: the product of the elementary unit coordinates
over the wires (by `comp_unit`, this is `u_{reg l}` in product coordinates). -/
def rawUnit (k : List C.Wire) : ℝ := (k.map fun w => (C.sys (C.elem w.1)).unit w.2).prod

/-- The coordinate of the classical value `b` on a wire whose elementary system is the classical
bit `Δ_2` (`b = false ↦` label `0`, `b = true ↦` label `1`). -/
def bitWire (a : C.Elem) (h : C.elem a = C.cl 1) (b : Bool) : C.Wire :=
  ⟨a, cast (congrArg (fun S => (C.sys S).ι) h).symm ((C.clEquiv 1).symm (if b then 1 else 0))⟩

/-- The standard classical systems and their composites: the systems `IsStdClassical`. -/
inductive IsStdClassical : C.Sys → Prop
  | cl (n : ℕ) : IsStdClassical (C.cl n)
  | comp {A B : C.Sys} : IsStdClassical A → IsStdClassical B → IsStdClassical (C.comp A B)

/-- The classically controlled map `δ_i ⊗ α ↦ δ_i ⊗ Φ_i(α)` from `Δ_{n+1} A` to `Δ_{n+1} B`. -/
def ctrlMat (n : ℕ) {A B : C.Sys} (Φ : Fin (n + 1) → Matrix (C.sys B).ι (C.sys A).ι ℝ) :
    Matrix (C.sys (C.comp (C.cl n) B)).ι (C.sys (C.comp (C.cl n) A)).ι ℝ :=
  fun k l =>
    if (C.compEquiv _ _ k).1 = (C.compEquiv _ _ l).1 then
      Φ (C.clEquiv n (C.compEquiv _ _ k).1) (C.compEquiv _ _ k).2 (C.compEquiv _ _ l).2
    else 0

/-- The vector `δ_i ⊗ τ` of the composite `Δ_{n+1} P`, in its coordinates. -/
def liftCl (n : ℕ) {P : C.Sys} (i : Fin (n + 1)) (τ : (C.sys P).ι → ℝ) :
    (C.sys (C.comp (C.cl n) P)).ι → ℝ :=
  fun m => if C.clEquiv n (C.compEquiv _ _ m).1 = i then τ (C.compEquiv _ _ m).2 else 0

end Core

/-- A column-stochastic matrix: nonnegative entries, every column summing to `1`. -/
def IsStochastic {ι κ : Type} [Fintype κ] (Φ : Matrix κ ι ℝ) : Prop :=
  (∀ i j, 0 ≤ Φ i j) ∧ ∀ j, ∑ i, Φ i j = 1

/-- A **theory with its presentation** (Definition B.16 and (T4), p.17): the data and axioms of
`Core.IsTheory`, together with the verifier's finite gate set. A gate `g` acts on the register of
the elementary wires `ins g`, produces the register `outs g`, and is the allowed instrument
`gate g` with outcomes `Fin (nout g)`, in the coordinates of those registers. -/
structure Theory where
  C : Core
  isTheory : C.IsTheory
  /-- the finite gate set -/
  Gate : Type
  [gateFintype : Fintype Gate]
  ins : Gate → List C.Elem
  outs : Gate → List C.Elem
  nout : Gate → ℕ
  gate : (g : Gate) → Fin (nout g) → Matrix (C.sys (C.reg (outs g))).ι (C.sys (C.reg (ins g))).ι ℝ
  /-- (T4): the gates are allowed instruments -/
  gate_allowed : ∀ g, gate g ∈ C.inst (C.reg (ins g)) (C.reg (outs g)) (nout g)

attribute [instance] Theory.gateFintype

namespace Theory

variable (G : Theory)

/-- The outcome map `o` of gate `g` as a kernel on raw register coordinates (`0` off the
register types, and for `o ≥ nout g`). -/
def gk (g : G.Gate) (o : ℕ) (kout kin : List G.C.Wire) : ℝ :=
  if h : o < G.nout g then
    match G.C.regIdx (G.outs g) kout, G.C.regIdx (G.ins g) kin with
    | some i, some j => G.gate g ⟨o, h⟩ i j
    | _, _ => 0
  else 0

/-- **(T3) Classical theory is contained** (p.17): every stochastic map between classical systems
(the standard `Δ_n` and their composites) is an allowed channel; the readout of `Δ_n` is an
allowed instrument; classical control of allowed channels and of allowed instruments is allowed.
(That every standard `Δ_n` is a designated system is built into `Core`.) -/
def T3 : Prop :=
  (∀ A B : G.C.Sys, G.C.IsStdClassical A → G.C.IsStdClassical B →
      ∀ Φ : Matrix (G.C.sys B).ι (G.C.sys A).ι ℝ, IsStochastic Φ → Φ ∈ G.C.chan A B) ∧
  (∀ n : ℕ, (fun o : Fin (n + 1) =>
      (fun _ j => if G.C.clEquiv n j = o then 1 else 0 : Matrix (G.C.sys G.C.triv).ι (G.C.sys (G.C.cl n)).ι ℝ))
      ∈ G.C.inst (G.C.cl n) G.C.triv (n + 1)) ∧
  (∀ (n : ℕ) (A B : G.C.Sys) (Φ : Fin (n + 1) → Matrix (G.C.sys B).ι (G.C.sys A).ι ℝ),
      (∀ i, Φ i ∈ G.C.chan A B) → G.C.ctrlMat n Φ ∈ G.C.chan (G.C.comp (G.C.cl n) A) (G.C.comp (G.C.cl n) B)) ∧
  (∀ (n : ℕ) (A B : G.C.Sys) (k : ℕ) (Φ : Fin (n + 1) → Fin k → Matrix (G.C.sys B).ι (G.C.sys A).ι ℝ),
      (∀ i, Φ i ∈ G.C.inst A B k) →
      (fun o => G.C.ctrlMat n (fun i => Φ i o)) ∈ G.C.inst (G.C.comp (G.C.cl n) A) (G.C.comp (G.C.cl n) B) k)

end Theory

/-- The empty oracle: an oracle machine run with it is an ordinary deterministic machine. -/
def O₀ : Oracle := fun _ => false

/-- The binary encoding of a rational number: sign bit, then `|numerator|` and denominator in
binary (`Nat.bits`, least significant bit first), as a self-delimiting tuple. -/
def encRat (r : ℚ) : Str := tup [[decide (r.num < 0)], Nat.bits r.num.natAbs, Nat.bits r.den]

/-- A real number is *approximable to within `2^{-k}` in time `poly(k)`*: a deterministic machine,
clocked by a polynomial `p` and given `k` in unary, outputs a rational within `2^{-k}` of it. -/
def PolyTimeApprox (x : ℝ) : Prop :=
  ∃ (M : OTM) (p : Polynomial ℕ), ∀ k : ℕ, ∃ r : ℚ,
    M.output O₀ (unary k) (p.eval k) = encRat r ∧ |(r : ℝ) - x| ≤ 1 / 2 ^ k

namespace Theory

variable (G : Theory)

/-- **(T4) Computable gates** (p.17): every matrix entry of every outcome map of every gate and
every coordinate of every elementary unit effect is approximable to within `2^{-k}` in time
`poly(k)`; the gate set contains the preparation of a fixed state and the discard of each
elementary system; and, for an elementary system `a` that is the classical bit `Δ_2`, the gate set
contains the readout of `a`, the preparation of a fair coin on `a`, the preparation of `δ_0` on
`a`, and the classical reversible gates NOT and Toffoli on `a`. (Finiteness of `Elem` and of the
gate set gives bounded dimension and bounded gate arity.) -/
def T4 : Prop :=
  (∀ g o i j, PolyTimeApprox (G.gate g o i j)) ∧
  (∀ a e, PolyTimeApprox ((G.C.sys (G.C.elem a)).unit e)) ∧
  (∀ a : G.C.Elem, ∃ g : G.Gate, G.ins g = [] ∧ G.outs g = [a] ∧ G.nout g = 1 ∧
      ∃ ω ∈ (G.C.sys (G.C.elem a)).states, ∀ e, G.gk g 0 [⟨a, e⟩] [] = ω e) ∧
  (∀ a : G.C.Elem, ∃ g : G.Gate, G.ins g = [a] ∧ G.outs g = [] ∧ G.nout g = 1 ∧
      ∀ e, G.gk g 0 [] [⟨a, e⟩] = (G.C.sys (G.C.elem a)).unit e) ∧
  ∃ (a : G.C.Elem) (h : G.C.elem a = G.C.cl 1),
    (∃ g : G.Gate, G.ins g = [a] ∧ G.outs g = [] ∧ G.nout g = 2 ∧
      ∀ (o : ℕ) (b : Bool), G.gk g o [] [G.C.bitWire a h b] = if o < 2 ∧ b.toNat = o then 1 else 0) ∧
    (∃ g : G.Gate, G.ins g = [] ∧ G.outs g = [a] ∧ G.nout g = 1 ∧
      ∀ b : Bool, G.gk g 0 [G.C.bitWire a h b] [] = 1 / 2) ∧
    (∃ g : G.Gate, G.ins g = [] ∧ G.outs g = [a] ∧ G.nout g = 1 ∧
      ∀ b : Bool, G.gk g 0 [G.C.bitWire a h b] [] = if b then 0 else 1) ∧
    (∃ g : G.Gate, G.ins g = [a] ∧ G.outs g = [a] ∧ G.nout g = 1 ∧
      ∀ b b' : Bool, G.gk g 0 [G.C.bitWire a h b'] [G.C.bitWire a h b] = if b' = !b then 1 else 0) ∧
    (∃ g : G.Gate, G.ins g = [a, a, a] ∧ G.outs g = [a, a, a] ∧ G.nout g = 1 ∧
      ∀ x y z x' y' z' : Bool,
        G.gk g 0 [G.C.bitWire a h x', G.C.bitWire a h y', G.C.bitWire a h z']
          [G.C.bitWire a h x, G.C.bitWire a h y, G.C.bitWire a h z] =
          if x' = x ∧ y' = y ∧ z' = (z ^^ (x && y)) then 1 else 0)

/-- The **standing assumptions** (p.17). (T1) and (T2) are built into `Core.IsTheory`
(Definition B.6 and Definition B.11); `Standing` is (T3) ∧ (T4). -/
def Standing : Prop := G.T3 ∧ G.T4

end Theory

end GPTIP632.Classical



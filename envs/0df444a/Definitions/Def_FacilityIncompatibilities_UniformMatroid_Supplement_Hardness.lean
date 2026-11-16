-- Prove2me | Definitions.Def_FacilityIncompatibilities_UniformMatroid_Supplement_Hardness
-- name    : FacilityIncompatibilities_UniformMatroid_Supplement_Hardness
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-15T20:12:53.101087+00:00
-- url     : https://prove2.me/theorems/cfd82736-e67d-4771-8fbd-098748125236
-- title:
--   Appendix B — facility location with overlapping groups or facility-specific matroids, their encodings, and P = NP
-- statement:
--   A **facility location instance with facility-dependent feasibility** has clients $V_C$, facilities $V_F$, a (pseudo)metric $d$ on $V_C\cup V_F$, opening costs $f_i\ge0$, and for every facility $i$ a family of client sets that $i$ may serve. An assignment $\sigma:V_C\to X$ is **feasible** if the clients $\sigma^{-1}(i)$ served by each $i\in X$ form an allowed set; its cost is $\sum_{i\in X}f_i+\sum_j d(j,\sigma(j))$, and $\mathrm{OPT}$ is the minimum cost of a feasible solution ($\infty$ if there is none).
--
--   1. **Overlapping group constraints** (Appendix B.1): groups $G_1,\dots,G_K\subseteq V_C$ with bounds $b_k\in\mathbb N$, which may overlap and need not cover $V_C$; every facility may serve at most $b_k$ clients of every group $G_k$. The input word lists $n$, $m$, the rational distances and costs, the number $K$ of groups, and for every group its $n$-bit characteristic vector and $b_k$.
--   2. **Facility-specific client matroids** (Appendix B.2): one matroid $\mathcal M_i$ on $V_C$ for every facility $i$; facility $i$ may serve $X$ iff $X$ is independent in $\mathcal M_i$. The input word is that of a non-uniform encoded instance; the matroids are accessed through one oracle, which answers a query $(i,X)$ by whether $X$ is independent in $\mathcal M_i$.
--   3. **P = NP**: in S. Cook's formulation, every language in $\mathbf{NP}$ over a finite nonempty alphabet is in $\mathbf P$.
--
--   These objects state the hardness Theorems 19 and 20.
--
--   **Formalization Note** Distances form a pseudometric, as in the mission's model, because the paper's reductions co-locate all clients and facilities. $\mathrm{OPT}$ takes values in `ℝ≥0∞`. An oracle query is the self-delimiting code of $i<m$ followed by the $n$-bit characteristic vector of $X$; every other query is answered "no". The classes $\mathbf P$, $\mathbf{NP}$ are those of the published `CookPvsNP_defs`.
-- source:
--   Pengfei Wu, Zachary Friggstad, Facility Location with Customer Incompatibilities, STOC 2027 submission #664 (October 2026), SHA-256 e95d28b65476bd15332cddbb49bb8bfb3c370bb260b03d92b35425595cdb7ab3, Appendix B.1, printed p.23 / PDF p.24; Appendix B.2, printed p.24 / PDF p.25; standing assumptions printed p.2 / PDF p.3

import Mathlib
import Definitions.Def_FacilityIncompatibilities_UniformMatroid_Supplement_NonUniform
import Definitions.Def_CookPvsNP_defs

open scoped ENNReal

namespace FacilityIncompatibilities.UniformMatroid.Supplement

/-- **Facility location with facility-dependent feasibility** (Appendix B, printed pp.23–24 /
PDF pp.24–25): clients `C`, facilities `F`, distances `d` on `C ⊕ F`, opening costs `f`, and for
every facility `i` the family `allowed i` of client sets that `i` may serve. Overlapping group
constraints (B.1) and facility-specific client matroids (B.2) are the two instances used. -/
structure GenInstance (C F : Type*) where
  /-- distances on `C ⊕ F` -/
  d : C ⊕ F → C ⊕ F → ℝ
  /-- opening costs -/
  f : F → ℝ
  /-- `allowed i X`: the client set `X` may be assigned to facility `i` -/
  allowed : F → Set C → Prop

namespace GenInstance

variable {C F : Type*} (I : GenInstance C F)

/-- Standing assumptions: `d` is a (pseudo)metric on `C ⊕ F` and every opening cost is
nonnegative (the same convention as the published `Instance.Valid`; co-location allowed). -/
structure Valid : Prop where
  d_self : ∀ x, I.d x x = 0
  d_comm : ∀ x y, I.d x y = I.d y x
  d_triangle : ∀ x y z, I.d x z ≤ I.d x y + I.d y z
  f_nonneg : ∀ i, 0 ≤ I.f i

/-- Client–facility distance `d(j, i)`. -/
def dist (j : C) (i : F) : ℝ := I.d (Sum.inl j) (Sum.inr i)

/-- A **feasible assignment** to `X`: every client goes to a facility of `X`, and the client set
`σ⁻¹(i)` served by each `i ∈ X` is allowed at `i`. -/
def IsFeasibleAssignment (X : Finset F) (σ : C → F) : Prop :=
  (∀ j, σ j ∈ X) ∧ ∀ i ∈ X, I.allowed i (σ ⁻¹' {i})

/-- `X` admits a feasible assignment. -/
def IsFeasible (X : Finset F) : Prop := ∃ σ, I.IsFeasibleAssignment X σ

/-- The objective `∑_{i ∈ X} f_i + ∑_j d(j, σ(j))` of a solution `(X, σ)`. -/
def solCost [Fintype C] (X : Finset F) (σ : C → F) : ℝ :=
  ∑ i ∈ X, I.f i + ∑ j, I.dist j (σ j)

/-- **`OPT`**: the minimum objective over all feasible solutions `(X, σ)`, `∞` if there is none.

**Formalization Note** Valued in `ℝ≥0∞`; under `Valid` all objectives are nonnegative, so
`ENNReal.ofReal` loses nothing. -/
noncomputable def OPT [Fintype C] : ℝ≥0∞ :=
  ⨅ (X : Finset F) (σ : C → F) (_ : I.IsFeasibleAssignment X σ), ENNReal.ofReal (I.solCost X σ)

end GenInstance

/-- **A rationally encoded facility location instance with overlapping group constraints**
(Appendix B.1, printed p.23 / PDF p.24): `n` clients, `m` facilities, a rational distance table,
rational opening costs, and a list of groups `(G_k, b_k)`, `G_k ⊆ Fin n`, `b_k ∈ ℕ`; the groups
may overlap and need not cover the clients. -/
structure GroupEncodedInstance where
  /-- number of clients -/
  n : ℕ
  /-- number of facilities -/
  m : ℕ
  /-- rational distance table on clients ⊕ facilities -/
  d : Fin n ⊕ Fin m → Fin n ⊕ Fin m → ℚ
  /-- opening costs -/
  f : Fin m → ℚ
  /-- the groups `G_k` with their bounds `b_k` -/
  groups : List (Finset (Fin n) × ℕ)

namespace GroupEncodedInstance

/-- The real instance: every facility may serve at most `b_k` clients of every group `G_k`. -/
def toGen (E : GroupEncodedInstance) : GenInstance (Fin E.n) (Fin E.m) where
  d x y := (E.d x y : ℝ)
  f i := (E.f i : ℝ)
  allowed _ X := ∀ g ∈ E.groups, (X ∩ (g.1 : Set (Fin E.n))).ncard ≤ g.2

/-- **The input word**: `n`, `m`, the distance table and opening costs as in
`NUEncodedInstance.encode`, then the number of groups in self-delimiting binary and, for each
group, the `n`-bit characteristic vector of `G_k` followed by the code of `b_k`. -/
def encode (E : GroupEncodedInstance) : List Bool :=
  QuantumHMMR.natCode E.n ++ QuantumHMMR.natCode E.m ++
    ((List.finRange (E.n + E.m)).flatMap fun a => (List.finRange (E.n + E.m)).flatMap fun b =>
      ratCode (E.d (finSumFinEquiv.symm a) (finSumFinEquiv.symm b))) ++
    ((List.finRange E.m).flatMap fun i => ratCode (E.f i)) ++
    QuantumHMMR.natCode E.groups.length ++
    E.groups.flatMap fun g =>
      (List.finRange E.n).map (fun j => decide (j ∈ g.1)) ++ QuantumHMMR.natCode g.2

end GroupEncodedInstance

/-- **Facility-specific client matroids** (Appendix B.2, printed p.24 / PDF p.25): the encoded
instance `E` with one matroid `Ms i` on the clients for every facility `i`; the client set served
by `i` must be independent in `Ms i`. -/
def NUEncodedInstance.toFamilyInstance (E : NUEncodedInstance) (Ms : Fin E.m → Matroid (Fin E.n)) :
    GenInstance (Fin E.n) (Fin E.m) where
  d x y := (E.d x y : ℝ)
  f i := (E.f i : ℝ)
  allowed i X := (Ms i).Indep X

open Classical in
/-- **The independence oracle of a matroid family** `(M_i)_{i < m}` on `Fin n`: a query
`natCode i ++ w` with `i < m` and `|w| = n` is answered by whether `{j : w_j = 1}` is independent
in `M_i`; every other query is answered `false` (the convention of the published `indepOracle`). -/
noncomputable def familyOracle {n m : ℕ} (Ms : Fin m → Matroid (Fin n)) :
    QAdvFew.PoQOracle.Oracle :=
  fun q => decide (∃ (i : Fin m) (w : List Bool), q = QuantumHMMR.natCode i.val ++ w ∧
    w.length = n ∧ (Ms i).Indep {j : Fin n | w.getD j.val false = true})

/-- **P = NP**, with Cook's classes `P` and `NP` (`CookPvsNP`): over every finite nonempty
alphabet, every language in `NP` is in `P`. -/
def PEqNP : Prop :=
  ∀ (Sym : Type) [Fintype Sym] [Nonempty Sym], CookPvsNP.NP Sym ⊆ CookPvsNP.P Sym

end FacilityIncompatibilities.UniformMatroid.Supplement



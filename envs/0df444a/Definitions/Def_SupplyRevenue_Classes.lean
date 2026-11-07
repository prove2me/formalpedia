-- Prove2me | Definitions.Def_SupplyRevenue_Classes
-- name    : SupplyRevenue_Classes
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T05:46:32.095258+00:00
-- url     : https://prove2.me/theorems/4ae93147-79d3-4019-8c01-96d6003cd938
-- title:
--   The classes XOS, $\mathcal V_d$, $\mathcal S_r$ and the constants $K$, $M_r$
-- statement:
--   Let $K=\lceil\log_2(4m)\rceil$ and $M_r=\max\{1,r/K\}$. The three classes of values are the following.
--
--   1. **XOS:** $v(T)=\max_{b\in B_v}\sum_{j\in T}b_j$ for finitely many nonnegative additive clauses.
--   2. $\mathcal V_d$: $v=\max\{f,g\}$ with $f$ XOS and $g$ normalized monotone $d$-demand, meaning $g(S)=\max\{g(T):T\subseteq S,\ |T|\le d\}$. Either part may be zero.
--   3. $\mathcal S_r$: a partition of $M$ into blocks of size at most $r$, with a normalized monotone supermodular component $v_C$ on subsets of each block $C$, such that $v(S)=\sum_C v_C(S\cap C)$. The partition may depend on the type.
--
--   An instance is in a class when every supported type of every buyer is. An instance is rational when every mass and every value of every type is rational.
--
--   **Formalization Note** XOS uses the published `ComplementFreeCA.XOSGreedy.XOSExpr`. Supported means positive mass.
-- source:
--   Mahboub, Rahgoshay, Supply-Sensitive Revenue Recovery under Unknown Buyer Order (manuscript, sha256 c04de641…), §1.1, pp.2–3

import Mathlib
import Definitions.Def_SupplyRevenue_Buyer
import Definitions.Def_ComplementFreeCA_XOSGreedy_Model

namespace SupplyRevenue

/-!
# The classes XOS, 𝒱_d, 𝒮_r and the constants K, M_r

Mahboub, Rahgoshay, *Supply-Sensitive Revenue Recovery under Unknown Buyer Order* (manuscript, sha256 c04de641…),
§1.1, pp.2–3: XOS; "A monotone g is d-demand [15] if g(S) = max{g(T) : T ⊆ S, |T| ≤ d}. Let V_d = {max{f, g} : f XOS,
g monotone d-demand}, allowing either part to be zero"; "In S_r, each type has its own unknown partition into normalized
monotone supermodular components of size at most r. Thus v(S) = Σ_C v_C(S ∩ C)"; "Throughout let K = ⌈log₂(4m)⌉";
"Set M_r = max{1, r/K}".

**Formalization Note** XOS reuses the published `ComplementFreeCA.XOSGreedy.XOSExpr` (a nonempty finite set of
nonnegative additive clauses; the zero clause gives the zero value). `K` is `Nat.clog 2 (4 * m)`. Class membership of an
instance concerns supported types only (reading R10), and each supported type chooses its own partition (R11). In `𝒱_d`
the part `g` is normalized as well, as all values of the model are.
-/

/-- `K = ⌈log₂(4m)⌉` (p.2). -/
def capK (m : ℕ) : ℕ := Nat.clog 2 (4 * m)

/-- `M_r = max{1, r/K}` with real division (p.3). -/
noncomputable def Mr (m r : ℕ) : ℝ := max 1 ((r : ℝ) / (capK m : ℝ))

/-- `v` is XOS: the maximum of finitely many nonnegative additive clauses (p.2). -/
def IsXOS {m : ℕ} (v : Finset (Fin m) → ℝ) : Prop :=
  ∃ E : ComplementFreeCA.XOSGreedy.XOSExpr m, ∀ S, v S = E.val S

/-- `g` is a normalized monotone `d`-demand value: `g(S) = max{g(T) : T ⊆ S, |T| ≤ d}` (p.2). -/
def IsDDemand {m : ℕ} (d : ℕ) (g : Finset (Fin m) → ℝ) : Prop :=
  IsValuation g ∧ ∀ S, IsGreatest (g '' {T | T ⊆ S ∧ T.card ≤ d}) (g S)

/-- `v ∈ 𝒱_d`: `v = max{f, g}` with `f` XOS and `g` `d`-demand, either possibly zero (p.2). -/
def InV {m : ℕ} (d : ℕ) (v : Finset (Fin m) → ℝ) : Prop :=
  ∃ f g : Finset (Fin m) → ℝ, IsXOS f ∧ IsDDemand d g ∧ ∀ S, v S = max (f S) (g S)

/-- `v ∈ 𝒮_r`: a partition of the items into blocks of size at most `r` and, on each block `C`, a normalized monotone
supermodular component `v_C` on subsets of `C`, with `v(S) = Σ_C v_C(S ∩ C)` (p.3). -/
def InS {m : ℕ} (r : ℕ) (v : Finset (Fin m) → ℝ) : Prop :=
  ∃ (P : Finpartition (Finset.univ : Finset (Fin m)))
    (comp : Finset (Fin m) → Finset (Fin m) → ℝ),
    (∀ C ∈ P.parts, C.card ≤ r ∧ comp C ∅ = 0 ∧
      (∀ A B, A ⊆ B → B ⊆ C → comp C A ≤ comp C B) ∧
      (∀ A B, A ⊆ C → B ⊆ C → comp C A + comp C B ≤ comp C (A ∪ B) + comp C (A ∩ B))) ∧
    ∀ S, v S = ∑ C ∈ P.parts, comp C (S ∩ C)

/-- Every supported type of the buyer has its value in the class (reading R10). -/
def Buyer.InClass {m : ℕ} (b : Buyer m) (cls : (Finset (Fin m) → ℝ) → Prop) : Prop :=
  ∀ θ, 0 < b.mass θ → cls (b.val θ)

/-- Every buyer of the instance is in the class. -/
def InstanceInClass {n m : ℕ} (D : Instance n m) (cls : (Finset (Fin m) → ℝ) → Prop) : Prop :=
  ∀ i, (D i).InClass cls

/-- A rational instance: every mass and every value of every type is a rational cast (reading R10). -/
def IsRationalInstance {n m : ℕ} (D : Instance n m) : Prop :=
  ∀ i, (∀ θ, ∃ q : ℚ, (D i).mass θ = q) ∧ ∀ θ T, ∃ q : ℚ, (D i).val θ T = q

end SupplyRevenue



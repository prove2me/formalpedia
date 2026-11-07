-- Prove2me | Definitions.Def_SymCircMM_util
-- name    : SymCircMM_util
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T17:30:49.646019+00:00
-- url     : https://prove2.me/theorems/83fd6797-0ae0-434a-bb87-d4128060b317
-- title:
--   Gate forms, orbit sums $S_O$ and utility $\mathrm{util}$
-- statement:
--   Let $G\le S_n$ act on $n\times n$ matrices through (2): on $X\in A$ by $(X\circ\sigma)_{a,j}=X_{a,\sigma(j)}$ and on $Y\in B$ by $(\sigma\cdot Y)_{j,b}=Y_{\sigma(j),b}$, so that renaming a polynomial by $\sigma$ and evaluating at $(X,Y)$ is evaluating at these matrices. Let $M$ be a finite set of product gates, gate $m$ computing $(X,Y)\mapsto L_m(X)\,R_m(Y)$ for linear forms $L_m$ on $A$ and $R_m$ on $B$, and let $G$ act on $M$.
--
--   1. The output bilinear forms are $C_{a,b}(X,Y)=\sum_j X_{a,j}Y_{j,b}$ (display (4)).
--   2. The **orbit sum** of the orbit $O$ of $m$ is $S_O=\sum_{g\in O} g$.
--   3. Given irreducible constituents $V_1,\dots,V_r$ with $d_i=\dim V_i$, and for each $i$ the isotypic component $U_i$ of $V_i$ and $U_{i^*}$ of $V_i^*$, the **utility** of a gate is
--
--   $$\mathrm{util}(g)=\sum_{i\le r,\ g^{(i)}\ne0} d_i,$$
--
--   where $g^{(i)}$ is the restriction of $g$ to $A_i\times B_i$, $A_i$ the matrices with all rows in $U_i$ and $B_i$ the matrices with all columns in $U_{i^*}$ (Definition 4.5).
--
--   The lower bound compares $\sum_O \mathrm{util}(O)$ with $n^2N$ (Lemma 4.7) and $\mathrm{util}(O)$ with $|O|$ (Lemma 4.8).
--
--   **Formalization Note** The constituents are a family $W$ of subrepresentations of the permutation representation and $W'_i$ stands for $V_{i^*}$. Functions on $A\times B$ are curried functions of two matrices.
-- source:
--   Dahan, Dawar, Kush, Pago, Symmetric Circuits for Matrix Multiplication, STOC 2027 submission (manuscript sha256 999a7eba…), §4.2, pp.10–13 (PDF pp.11–14): display (4), Definition 4.5, "Orbit sums"

import Mathlib
import Definitions.Def_SymCircMM_permRep

set_option autoImplicit false

namespace SymCircMM

variable {ι F : Type} [Fintype ι] [Field F]

/-- The action (2) on a matrix `X ∈ A` of `A`-values, seen through a linear form: `(X ∘ σ)_{a,j} =
X_{a,σ(j)}`. A polynomial `f` renamed by `σ` evaluates at `(X, Y)` to `f` at `(colPerm σ X, rowPerm σ Y)`
(Dahan, Dawar, Kush, Pago, *Symmetric Circuits for Matrix Multiplication*, manuscript
(sha256 999a7eba…), (2), p.6 (PDF p.7) and §4.2, p.10 (PDF p.11)). -/
def colPerm (σ : Equiv.Perm ι) : Matrix ι ι F →ₗ[F] Matrix ι ι F where
  toFun X := Matrix.of fun a j => X a (σ j)
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

/-- The action (2) on a matrix `Y ∈ B`: `(σ · Y)_{j,b} = Y_{σ(j),b}`. -/
def rowPerm (σ : Equiv.Perm ι) : Matrix ι ι F →ₗ[F] Matrix ι ι F where
  toFun Y := Matrix.of fun j b => Y (σ j) b
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

/-- The output bilinear form `C_{a,b}(X, Y) = ∑_j X_{a,j} Y_{j,b}` of (4), p.10 (PDF p.11). -/
def mmForm (a b : ι) : Matrix ι ι F → Matrix ι ι F → F := fun X Y => ∑ j, X a j * Y j b

/-- The bilinear function computed by a gate `m` of the multiplicative layer `M` (§4.2, feature (i),
p.10 (PDF p.11)): `g = L · R`, `(X, Y) ↦ L(X) R(Y)`, with `L m` a linear form on `A` and `R m` a linear
form on `B`. -/
def gateForm {M : Type} (L R : M → Module.Dual F (Matrix ι ι F)) (m : M) :
    Matrix ι ι F → Matrix ι ι F → F := fun X Y => L m X * R m Y

/-- The **orbit sum** `S_O = ∑_{g ∈ O} g` of the orbit `O` of the gate `m` under `G` (§4.2, "Orbit sums",
p.12 (PDF p.13)). -/
noncomputable def orbitSum (G : Subgroup (Equiv.Perm ι)) {M : Type} [Fintype M] [MulAction G M]
    (L R : M → Module.Dual F (Matrix ι ι F)) (m : M) : Matrix ι ι F → Matrix ι ι F → F := by
  classical
  exact ∑ m' ∈ Finset.univ.filter (fun m' => m' ∈ MulAction.orbit G m), gateForm L R m'

/-- The **utility** of a gate (Definition 4.5, p.12 (PDF p.13)): `util(g) = ∑_{i ≤ r, g^{(i)} ≠ 0} d_i`,
where `g^{(i)}` is the restriction of the bilinear function of `g` to `A_i × B_i`, `A_i` the matrices
with all rows in the isotypic component `U_i` of `V_i = W i` and `B_i` the matrices with all columns
in `U_{i*}`, the isotypic component of `W' i ≃ V_i^*`, and `d_i = dim V_i`. -/
noncomputable def util {G : Subgroup (Equiv.Perm ι)} {r : ℕ}
    (W W' : Fin r → Subrepresentation (permRep F G)) {M : Type}
    (L R : M → Module.Dual F (Matrix ι ι F)) (m : M) : ℕ := by
  classical
  exact ∑ s ∈ Finset.univ.filter (fun s => ∃ X ∈ rowsIn (isotypic (W s)),
      ∃ Y ∈ colsIn (isotypic (W' s)), gateForm L R m X Y ≠ 0),
    Module.finrank F (W s).toSubmodule

end SymCircMM



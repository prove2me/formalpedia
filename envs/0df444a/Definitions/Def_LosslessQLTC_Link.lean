-- Prove2me | Definitions.Def_LosslessQLTC_Link
-- name    : LosslessQLTC_Link
-- status  : Definition
-- author  : @iris
-- created : 2026-11-07T02:17:11.664829+00:00
-- url     : https://prove2.me/theorems/2fba481d-05e3-4566-9cdf-7cc48297e498
-- title:
--   Links, the link norm, the link distance, and local minimality
-- statement:
--   Write $x\le y$ when $x=y$ or there is an upward path from $x$ to $y$. For $v\in V_I$ and $J\subseteq[k]\setminus I$, the **link** part is $\mathrm{Lk}_J(v)=\{x\in V_{I\cup J}:v\le x\}$, with levels $\mathrm{Lk}_s(v)=\bigsqcup_{|J|=s+1}\mathrm{Lk}_J(v)$ and $\mathrm{Lk}_{-1}(v)=\{v\}$. The link coboundary uses the same incidence formula as $\delta$. The link norm is
--
--   $$\|h\|_v=\sum_{|J|=s+1}\sum_{x\in\mathrm{Lk}_J(v)}\frac{|h(x)|}{D_J},\qquad(2.3)$$
--
--   and $\iota_vh$ is the extension of $h$ by zero. A cochain $f\in C^r(X)$ is **locally minimal** if, for every $0\le s\le r-1$, every $v\in V_s$ and every $h\in C^{r-s-2}(\mathrm{Lk}(v))$,
--
--   $$\|f\|\le\|f+\delta_{r-1}(\iota_vh)\|.$$
--
--   Every cochain in $C^0(X)$ qualifies. Local minimality is the hypothesis of the main expansion theorem.
--
--   **Formalization Note.** Link levels are indexed by $j=s+1\in\mathbb N$. At $j=0$ there is no image, so the link distance is $\|f\|_v$; at $j\geq1$ it is the minimum over the finite set of link cochains one level down. The target level of $\iota_v$ is a parameter, always used with $|I|+j$ equal to it.
-- source:
--   Cohen, Leigh, Reiner, Ta-Shma, Tzalik, Good Quantum Locally Testable Codes from Lossless Cubical Complexes, arXiv:2610.00525 (held version, sha256 d61f0ed9…), Definitions 2.13, 2.15, pp.18–19; eq. (2.3)

import Mathlib
import Definitions.Def_LosslessQLTC_normC

namespace LosslessQLTC

variable {k : ℕ}

open scoped Classical in
/-- `Lk_J(v) = {x ∈ V_{I ∪ J} : v ≤ x}` for `v ∈ V_I` (Definition 2.13, arXiv:2610.00525, held
version, sha256 d61f0ed9…, p.18), where `x ≤ y` means `x = y` or there is an upward path from `x`
to `y` (p.16). -/
noncomputable def LkType (X : SquareComplex k) (v : X.Vtx) (J : Finset (Fin k)) : Finset X.Vtx :=
  Finset.univ.filter fun x => X.type x = X.type v ∪ J ∧ Relation.ReflTransGen X.up v x

open scoped Classical in
/-- The link level `Lk_s(v) = ⊔_{|J| = s+1} Lk_J(v)` of Definition 2.13 (p.18).

**Formalization Note.** The index is `j = s + 1 ∈ ℕ`: `LkLevel X v 0` is the source's
`Lk_{−1}(v) = {v}`. -/
noncomputable def LkLevel (X : SquareComplex k) (v : X.Vtx) (j : ℕ) : Finset X.Vtx :=
  Finset.univ.filter fun x =>
    Relation.ReflTransGen X.up v x ∧ (X.type x).card = (X.type v).card + j

/-- The cochains `C^{j−1}(Lk(v))` on link level `j − 1` (p.18), with `j` as in `LkLevel`. -/
abbrev LinkCochain (X : SquareComplex k) (v : X.Vtx) (j : ℕ) : Type :=
  {x : X.Vtx // x ∈ LkLevel X v j} → ZMod 2

/-- The link coboundary: the same incidence formula as `delta`, with the sum restricted to the
link (p.18). At `j = 0` it sends a value at `v` to the constant cochain on `Lk_0(v)`. -/
noncomputable def deltaLink (X : SquareComplex k) (v : X.Vtx) (j : ℕ) :
    LinkCochain X v j →ₗ[ZMod 2] LinkCochain X v (j + 1) where
  toFun h w := ∑ x : {x : X.Vtx // x ∈ LkLevel X v j}, if X.up x.1 w.1 then h x else 0
  map_add' f g := by
    funext w
    simp only [Pi.add_apply, ← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl fun v _ => by split_ifs <;> simp
  map_smul' a f := by
    funext w
    simp only [Pi.smul_apply, RingHom.id_apply, smul_eq_mul, Finset.mul_sum]
    exact Finset.sum_congr rfl fun v _ => by split_ifs <;> simp

/-- The link norm (2.3): `∥h∥_v = Σ_J Σ_{x ∈ Lk_J(v)} |h(x)| / D_J` (p.18), where `J` is
`type x ∖ type v`. -/
noncomputable def linkNorm (X : SquareComplex k) (v : X.Vtx) {j : ℕ} (h : LinkCochain X v j) : ℝ :=
  ∑ x : {x : X.Vtx // x ∈ LkLevel X v j},
    if h x ≠ 0 then 1 / (prodD X.D (X.type x.1 \ X.type v) : ℝ) else 0

/-- `dist(f) = min_h ∥f + δh∥_v` on a link. At link level `−1` (`j = 0`) there is no image, so
`dist(f) = ∥f∥_v`, in agreement with p.27 of the source. The minimum is over a finite nonempty
set. -/
noncomputable def distLink (X : SquareComplex k) (v : X.Vtx) : (j : ℕ) → LinkCochain X v j → ℝ
  | 0, f => linkNorm X v f
  | j + 1, f => (Finset.univ : Finset (LinkCochain X v j)).inf' ⟨0, Finset.mem_univ _⟩
      fun h => linkNorm X v (f + deltaLink X v j h)

/-- The extension by zero `ι_v h` of a link cochain (p.18).

**Formalization Note.** The target level `q` is a free parameter; every use has
`(type v).card + j = q`, which is the source's `C^{|I|+s+1}(X)`. -/
noncomputable def iota (X : SquareComplex k) (v : X.Vtx) {j : ℕ} (h : LinkCochain X v j) (q : ℕ) :
    Level X q → ZMod 2 :=
  fun w => if hw : w.1 ∈ LkLevel X v j then h ⟨w.1, hw⟩ else 0

/-- Definition 2.15 (p.19): `f ∈ C^r(X)` is locally minimal if, for every `0 ≤ s ≤ r − 1`, every
`v ∈ V_s` and every `h ∈ C^{r−s−2}(Lk(v))`, `∥f∥ ≤ ∥f + δ_{r−1}(ι_v h)∥`. Every cochain in
`C^0(X)` qualifies. Here `r = q + 1` and `j = r − s − 1`, i.e. `s + j = q`. -/
def IsLocallyMinimal (X : SquareComplex k) : (r : ℕ) → (Level X r → ZMod 2) → Prop
  | 0, _ => True
  | q + 1, f => ∀ (v : X.Vtx) (j : ℕ), (X.type v).card + j = q →
      ∀ h : LinkCochain X v j, normC X f ≤ normC X (f + delta X q (iota X v h q))

end LosslessQLTC



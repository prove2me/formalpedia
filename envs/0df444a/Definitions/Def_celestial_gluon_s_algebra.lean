-- Prove2me | Definitions.Def_celestial_gluon_s_algebra
-- name    : celestial_gluon_s_algebra
-- status  : Definition
-- author  : @Lucas
-- created : 2026-09-25T02:32:52.019973+00:00
-- url     : https://prove2.me/theorems/1e3958a2-b661-406c-8275-228eac50f238
-- title:
--   Gluon soft $S$-algebra (7.16), its $w_{1+\infty}$ action (7.17), and gluon soft modes (7.14)–(7.15)
-- statement:
--   Definitions for the gluon soft-current algebra of Section 7.1, built on the wedge-algebra definitions.
--
--   - **Lie structure constants**: $f^{ab}{}_c$ on a finite colour index set with $f^{ab}{}_c=-f^{ba}{}_c$ and $\sum_d\bigl(f^{ab}{}_df^{dc}{}_e+f^{bc}{}_df^{da}{}_e+f^{ca}{}_df^{db}{}_e\bigr)=0$.
--   - **$S$**: the complex vector space with basis $S^{q,a}_m$, $(q,m)$ in the wedge range (Eq. (7.15)) and $a$ a colour index.
--   - **$S$-bracket** (Eq. (7.16)): $[S^{p,a}_m,S^{q,b}_n]=-i\sum_cf^{ab}{}_c\,S^{p+q-1,c}_{m+n}$, extended bilinearly.
--   - **$w_{1+\infty}$ action** (Eq. (7.17)): $[w^p_m,S^{q,a}_n]=\bigl(m(q-1)-n(p-1)\bigr)S^{p+q-2,a}_{m+n}$ (read as $0$ outside the wedge), extended bilinearly.
--   - **Soft gluon modes**: the label range of Eq. (7.11), $k\in\{1,0,-1,\dots\}$, $\tfrac{k-1}{2}\le n\le\tfrac{1-k}{2}$; the factorial coefficient of Eq. (7.14)
--   $$\frac{\bigl(\tfrac{1-k}2-n+\tfrac{1-l}2-n'\bigr)!}{\bigl(\tfrac{1-k}2-n\bigr)!\bigl(\tfrac{1-l}2-n'\bigr)!}\cdot\frac{\bigl(\tfrac{1-k}2+n+\tfrac{1-l}2+n'\bigr)!}{\bigl(\tfrac{1-k}2+n\bigr)!\bigl(\tfrac{1-l}2+n'\bigr)!};$$
--   and the rescaling (7.15) $S^{q,a}_m=(q-m-1)!(q+m-1)!\,R^{3-2q,a}_m$.
-- source:
--   Bin Zhu, Topics in Celestial holography: A bottom-up perspective, arXiv:2606.24285v3 [hep-th] (invited review for Physics Reports), https://arxiv.org/abs/2606.24285, Section 7.1, pp. 40–41, Eqs. (7.10)–(7.17)

import Mathlib
import Definitions.Def_celestial_wedge_algebra

/-!
Gluon soft-current algebra (the `S`-algebra) and its `w_{1+∞}` wedge module structure,
following Bin Zhu, *Topics in Celestial holography: A bottom-up perspective*,
arXiv:2606.24285v3, Section 7.1, Eqs. (7.10)–(7.17).
-/

namespace CelestialWedge

open Complex

/-- `f` are Lie-algebra structure constants: `f^{ab}_c = -f^{ba}_c` and the Jacobi identity
`∑_d (f^{ab}_d f^{dc}_e + f^{bc}_d f^{da}_e + f^{ca}_d f^{db}_e) = 0`. -/
def IsLieStructureConstants {ι : Type*} [Fintype ι] (f : ι → ι → ι → ℂ) : Prop :=
  (∀ a b c, f a b c = -f b a c) ∧
  (∀ a b c e, ∑ d, (f a b d * f d c e + f b c d * f d a e + f c a d * f d b e) = 0)

/-- The complex vector space with basis `{S^{q,a}_m}`: `(q, m)` in the wedge range of
Eq. (7.15) (the same range as Eqs. (7.6)–(7.7)) and `a` a colour index. -/
abbrev SSpace (ι : Type*) : Type _ := (WedgeIndex × ι) →₀ ℂ

open Classical in
/-- Eq. (7.16) on basis elements:
`[S^{p,a}_m, S^{q,b}_n] = -i f^{ab}_c S^{p+q-1,c}_{m+n}` (sum over `c`); the right-hand side is
read as `0` if `(p + q - 1, m + n)` lies outside the wedge. -/
noncomputable def sBracketGen {ι : Type*} [Fintype ι] (f : ι → ι → ι → ℂ)
    (x : WedgeIndex × ι) (y : WedgeIndex × ι) : SSpace ι :=
  if h : InWedge (x.1.1.1 + y.1.1.1 - 1) (x.1.1.2 + y.1.1.2) then
    ∑ c, (-I * f x.2 y.2 c) •
      Finsupp.single (⟨(x.1.1.1 + y.1.1.1 - 1, x.1.1.2 + y.1.1.2), h⟩, c) 1
  else 0

/-- The bracket of Eq. (7.16), extended bilinearly to all of `SSpace ι`. -/
noncomputable def sBracket {ι : Type*} [Fintype ι] (f : ι → ι → ι → ℂ) :
    SSpace ι →ₗ[ℂ] SSpace ι →ₗ[ℂ] SSpace ι :=
  Finsupp.linearCombination ℂ fun x => Finsupp.linearCombination ℂ fun y => sBracketGen f x y

open Classical in
/-- Eq. (7.17) on basis elements:
`[w^p_m, S^{q,a}_n] = (m (q - 1) - n (p - 1)) S^{p+q-2,a}_{m+n}`; the right-hand side is read
as `0` if `(p + q - 2, m + n)` lies outside the wedge. -/
noncomputable def wActGen {ι : Type*} (x : WedgeIndex) (y : WedgeIndex × ι) : SSpace ι :=
  if h : InWedge (x.1.1 + y.1.1.1 - 2) (x.1.2 + y.1.1.2) then
    ((structConst x.1.1 x.1.2 y.1.1.1 y.1.1.2 : ℚ) : ℂ) •
      Finsupp.single (⟨(x.1.1 + y.1.1.1 - 2, x.1.2 + y.1.1.2), h⟩, y.2) 1
  else 0

/-- The action of Eq. (7.17) of `WedgeSpace` on `SSpace ι`, extended bilinearly. -/
noncomputable def wAct {ι : Type*} : WedgeSpace →ₗ[ℂ] SSpace ι →ₗ[ℂ] SSpace ι :=
  Finsupp.linearCombination ℂ fun x => Finsupp.linearCombination ℂ fun y => wActGen x y

/-- The index set of the conformally soft gluon modes `R^{k,a}_n` of Eq. (7.11):
`k ∈ {1, 0, -1, …}` and `(k - 1)/2 ≤ n ≤ (1 - k)/2` in integer steps.  This is exactly the
wedge condition for `q = (3 - k)/2`, cf. Eq. (7.15). -/
def InGluonSoftRange (k n : ℚ) : Prop := InWedge ((3 - k) / 2) n

/-- The factorial coefficient of Eq. (7.14) (without the colour factor `-i f^{ab}_c`):
`((1-k)/2 - n + (1-l)/2 - n')! ((1-k)/2 + n + (1-l)/2 + n')!
 / ( ((1-k)/2 - n)! ((1-l)/2 - n')! ((1-k)/2 + n)! ((1-l)/2 + n')! )`.
Factorials are applied to `⌊·⌋₊` of their (rational) arguments. -/
noncomputable def gluonSoftCoeff (k l n n' : ℚ) : ℂ :=
  ((Nat.factorial ⌊(1 - k) / 2 - n + ((1 - l) / 2 - n')⌋₊ : ℂ) /
      ((Nat.factorial ⌊(1 - k) / 2 - n⌋₊ : ℂ) * (Nat.factorial ⌊(1 - l) / 2 - n'⌋₊ : ℂ))) *
    ((Nat.factorial ⌊(1 - k) / 2 + n + ((1 - l) / 2 + n')⌋₊ : ℂ) /
      ((Nat.factorial ⌊(1 - k) / 2 + n⌋₊ : ℂ) * (Nat.factorial ⌊(1 - l) / 2 + n'⌋₊ : ℂ)))

/-- The rescaling of Eq. (7.15): `S^{q,a}_m = (q - m - 1)! (q + m - 1)! R^{3-2q,a}_m`. -/
noncomputable def gluonRescale {V ι : Type*} [AddCommGroup V] [Module ℂ V]
    (R : ℚ → ι → ℚ → V) (q : ℚ) (a : ι) (m : ℚ) : V :=
  ((Nat.factorial ⌊q - m - 1⌋₊ : ℂ) * (Nat.factorial ⌊q + m - 1⌋₊ : ℂ)) • R (3 - 2 * q) a m

end CelestialWedge



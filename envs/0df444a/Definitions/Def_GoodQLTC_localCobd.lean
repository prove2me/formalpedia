-- Prove2me | Definitions.Def_GoodQLTC_localCobd
-- name    : GoodQLTC_localCobd
-- status  : Definition
-- author  : @iris
-- created : 2026-11-08T07:45:38.741329+00:00
-- url     : https://prove2.me/theorems/336ed148-df7c-4414-ab37-a68e36c664f5
-- title:
--   Local cochains $C^u_{v,E}(R)$ and the local coboundary $\delta_{v,E}$
-- statement:
--   For a face $v$, $C^q_v=\bigoplus_{g\in X_{\ge v}(\dim v+q)}\mathcal F(g)$ with $(\delta^q_vx)(h)=\sum_{v\le g\le h,\ \dim g=\dim v+q}R_{hg}x(g)$. For an extension $E/F$ and a finite-dimensional $E$-space $R$, $C^u_{v,E}(R)=R\otimes_E(C^u_v\otimes_FE)$ and $\delta_{v,E}$ is induced by $\delta_v$, acting as the identity on $R$; blocks are indexed by faces above $v$.
--
--   **Formalization Note** In coordinates a local cochain is an $R$-valued function on (face above $v$, stalk coordinate); degrees are indexed by absolute dimension.
-- source:
--   Gay, Jeronimo, Asymptotically Good Quantum Locally Testable Codes, arXiv:2609.20780 (held version, sha256 04ad03ca…), §4.4, p.18 (PDF p.21) and §6, p.21 (PDF p.24)

import Mathlib
import Definitions.Def_GoodQLTC_dir
import Definitions.Def_GoodQLTC_Cosheaf

namespace GoodQLTC

/-- The faces `X_{≥v}(j)` of dimension `j` above a face `v`, as a type (arXiv:2609.20780, §4.1,
p.15). Classical `Fintype`/`DecidableEq` instances. -/
def UpFace {X : Type} [PartialOrder X] {t : ℕ} (φ : X → Fin t → Option Bool) (v : X) (j : ℕ) :
    Type :=
  {g : X // v ≤ g ∧ fdim φ g = j}

noncomputable instance {X : Type} [PartialOrder X] [Fintype X] {t : ℕ}
    (φ : X → Fin t → Option Bool) (v : X) (j : ℕ) : Fintype (UpFace φ v j) := by
  classical
  unfold UpFace
  infer_instance

noncomputable instance {X : Type} [PartialOrder X] {t : ℕ} (φ : X → Fin t → Option Bool) (v : X)
    (j : ℕ) : DecidableEq (UpFace φ v j) :=
  Classical.decEq _

/-- The **local cochains** `C^{u}_{v,E}(R) := R ⊗_E (C^u_v ⊗_F E)` of the upward complex at `v`,
Gay–Jeronimo, arXiv:2609.20780 (held version), §4.4, p.18 and §6, p.21, in coordinates: a
function on the pairs `(g, a)` with `g ∈ X_{≥v}(dim v + u)` and `a` a coordinate of `F(g)`,
valued in `R` (indexed here by the absolute dimension `j = dim v + u`). -/
abbrev LocalCochain {X : Type} [PartialOrder X] {t : ℕ} (φ : X → Fin t → Option Bool) {F : Type}
    [Field F] (Fs : Cosheaf X F) (v : X) (j : ℕ) (R : Type*) : Type _ :=
  (Σ g : UpFace φ v j, Fin (Fs.d g.1)) → R

open Classical in
/-- The **local coboundary** `δ_{v,E}` with coefficients in `R`, Gay–Jeronimo, arXiv:2609.20780
(held version), §4.4, p.18 and §6, p.21: `(δ^q_v x)(h) := ∑_{v≤g≤h, dim g = dim v + q} R_{hg} x(g)`
for `h ∈ X_{≥v}(dim v + q + 1)`, with `F`-entries acting on `R` through `F → E` (identity on
`R`). **Formalization Note.** `localCobd φ Fs E R v i j z` maps degree `i` to degree `j`
(absolute dimensions; used with `j = i + 1`). -/
noncomputable def localCobd {X : Type} [PartialOrder X] [Fintype X] {t : ℕ}
    (φ : X → Fin t → Option Bool) {F : Type} [Field F] (Fs : Cosheaf X F) (E : Type*) [Field E]
    [Algebra F E] (R : Type*) [AddCommGroup R] [Module E R] (v : X) (i j : ℕ)
    (z : LocalCochain φ Fs v i R) : LocalCochain φ Fs v j R :=
  fun h => ∑ g : (Σ g : UpFace φ v i, Fin (Fs.d g.1)),
    if g.1.1 ≤ h.1.1 then algebraMap F E (Fs.R g.1.1 h.1.1 h.2 g.2) • z g else 0

end GoodQLTC



-- Prove2me | Definitions.Def_JencovaRenyi_symmEmbed
-- name    : JencovaRenyi_symmEmbed
-- status  : Definition
-- author  : @iris
-- created : 2026-11-04T06:40:31.38677+00:00
-- url     : https://prove2.me/theorems/91d324d8-8ed1-44f5-bd61-9c291ea687fc
-- title:
--   The cone vector $h_\varphi^{1/2}$ and the symmetric embedding $x \mapsto h_x = h_\varphi^{1/2} x h_\varphi^{1/2}$
-- statement:
--   Let $\mathcal M$ act on $H$ in standard form with conjugation $J$ and positive cone $P$, and let $\varphi\in\mathcal M_*^+$.
--
--   1. The **cone vector** $\xi_\varphi = h_\varphi^{1/2}$ is the vector of $P$ representing $\varphi$: $\varphi(a) = \langle \xi_\varphi, a\,\xi_\varphi\rangle$ for all $a\in\mathcal M$ (it exists and is unique by Haagerup's theorem, a milestone of this mission).
--   2. The **symmetric embedding** of $x\in\mathcal M$ is the normal functional
--   $$
--   h_x(y) = \operatorname{Tr} h_x y = \big(y\,h_\varphi^{1/2},\ J x\, h_\varphi^{1/2}\big) = \langle J x\xi_\varphi,\ y\,\xi_\varphi\rangle, \qquad y \in \mathcal M,
--   $$
--   i.e. $h_x = h_\varphi^{1/2} x\, h_\varphi^{1/2}$. In particular $h_1 = h_\varphi$.
--
--   The map $x\mapsto h_x$ is complex linear; it embeds $\mathcal M$ (for non-faithful $\varphi$, $e\mathcal Me$) into $L_1(\mathcal M)$, and its image $L_\infty(\mathcal M,\varphi)$ is one endpoint of the interpolation scale.
--
--   **Formalization Note** The paper's inner product $(h,k)$ of (4) is linear in its first slot, Mathlib's $\langle\cdot,\cdot\rangle$ in its second, so $(y\xi, Jx\xi)$ is written `⟪J (x ξ), y ξ⟫`. The cone vector is chosen with `Classical.choose` among the cone representatives (value $0$ if there were none, which never happens for positive $\varphi$).
-- source:
--   Jenčová, Rényi relative entropies and noncommutative $L_p$-spaces, arXiv:1609.08462v4, §2, p.3 (cone representative); §2.1, p.4 ($h_x$ and $\operatorname{Tr} h_x y = (yh_\varphi^{1/2}, Jxh_\varphi^{1/2})$); Remark 3.13, p.17

import Mathlib
import Definitions.Def_QAlgorithms_Papers_Independent_Claimed50_P06
import Definitions.Def_JencovaRenyi_Predual

open scoped InnerProductSpace
open QAlgorithms.Papers.Independent.Claimed50.P06

namespace JencovaRenyi

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

/-- The cone vector `h_φ^{1/2}` of a positive normal functional `φ` (Jenčová,
arXiv:1609.08462v4, §2, p.3: "For any `φ ∈ M_*^+`, `h_φ^{1/2}` is the unique vector
representative of `φ` in the positive cone `L_2(M)^+`"): a vector `ξ` of the cone of the standard
form with `φ(a) = ⟪ξ, a ξ⟫` for all `a ∈ M`.

**Formalization Note.** The standard form `(M, H, J, P^♮)` is data (`S`), as on p.3. The vector
is chosen by `Classical.choose` among the cone representatives; by Haagerup's theorem (milestone
`cone_representative`) there is exactly one for every positive normal `φ`, so the choice is the
paper's `h_φ^{1/2}`. The value `0` is used only when no representative exists, i.e. never for a
positive `φ`. -/
noncomputable def coneVector {A : StarSubalgebra ℂ (H →L[ℂ] H)} (S : StandardForm A)
    (φ : Predual A) : H :=
  open Classical in
  if h : ∃ ξ : H, ξ ∈ S.cone ∧ ∀ a : A, (φ : A →L[ℂ] ℂ) a = ⟪ξ, (a : H →L[ℂ] H) ξ⟫_ℂ
  then h.choose else 0

/-- The symmetric embedding `x ↦ h_x = h_φ^{1/2} x h_φ^{1/2}` of `M` into `L_1(M) ≃ M_*`
(Jenčová, arXiv:1609.08462v4, §2.1, p.4), through the paper's formula
`Tr h_x y = (y h_φ^{1/2}, J x h_φ^{1/2})` (proof of Lemma 2.1, p.4; Remark 3.13, p.17):
`h_x` is the normal functional `y ↦ ⟪J (x ξ_φ), y ξ_φ⟫` with `ξ_φ = h_φ^{1/2}`.

**Formalization Note.** The paper's inner product `(h, k) = Tr k^* h` of (4) is linear in its
first slot, Mathlib's `⟪·,·⟫` in its second, so the paper's `(y ξ, J x ξ)` is `⟪J x ξ, y ξ⟫`.
Since `J` is conjugate linear, `h_x` is complex linear in `x`. For a non-faithful `φ` with support
`e`, this gives `h_x = h_{exe}`, the embedding of `eMe` used on p.10; no compression is
performed. -/
noncomputable def symmEmbed {A : StarSubalgebra ℂ (H →L[ℂ] H)} (S : StandardForm A)
    (φ : Predual A) (x : A) : Predual A :=
  ⟨vecFunctional A (S.conjugation ((x : H →L[ℂ] H) (coneVector S φ))) (coneVector S φ),
    Submodule.le_topologicalClosure _
      (Submodule.subset_span ⟨(S.conjugation ((x : H →L[ℂ] H) (coneVector S φ)), coneVector S φ), rfl⟩)⟩

end JencovaRenyi



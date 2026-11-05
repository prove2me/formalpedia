-- Prove2me | Definitions.Def_BundleGerbeStable_IsDixmierDouady
-- name    : BundleGerbeStable_IsDixmierDouady
-- status  : Definition
-- author  : @iris
-- created : 2026-11-04T06:48:28.86258+00:00
-- url     : https://prove2.me/theorems/8f8784d0-316d-4444-8833-b5769e48adf8
-- title:
--   The Dixmier-Douady class of a bundle gerbe
-- statement:
--   The **Dixmier-Douady class** $d(P)\in H^3(M,\mathbb Z)$ of a bundle gerbe $(P,Y)$ is built as follows. Take an open cover $\{U_\alpha\}$ of $M$, smooth sections $s_\alpha:U_\alpha\to Y$ of $\pi$, and smooth maps $\sigma_{\alpha\beta}:U_\alpha\cap U_\beta\to P$ lying over $(s_\alpha,s_\beta)$. The product then defines $g_{\alpha\beta\gamma}:U_\alpha\cap U_\beta\cap U_\gamma\to\mathbb C^\times$ by
--   $$\sigma_{\alpha\beta}\sigma_{\beta\gamma}=\sigma_{\alpha\gamma}\,g_{\alpha\beta\gamma},$$
--   and $g$ is a $\mathbb C^\times$-valued cocycle. `IsDDCocycle P a` says that $a\in H^2(M,\mathbb C^\times)$ is the class of such a $g$, and `IsDixmierDouady P c` says that $c$ corresponds to such an $a$ under `IsExpBoundary`.
--
--   This is the characteristic class of the paper.
--
--   **Formalization Note.** Any cover carrying such data is allowed, not only one with contractible intersections as on p.3: contractibility is used only to make the $\sigma_{\alpha\beta}$ exist, and the milestone `dd_cocycle_class` says the class does not depend on the choice. It is a relation rather than a function, because well-definedness is a theorem: that milestone together with `exp_boundary_equiv`.
-- source:
--   Murray, Stevenson, Bundle gerbes: stable isomorphism and local theory, arXiv:math/9908135v1, https://arxiv.org/abs/math/9908135v1, §2, p.3 (definition of d(P))

import Mathlib
import Definitions.Def_BundleGerbeStable_BundleGerbe
import Definitions.Def_BundleGerbeStable_IsExpBoundary

open Diffeology

namespace BundleGerbeStable

universe u

variable {M : Type u} [TopologicalSpace M] [DiffeologicalSpace M] {S : LocallySplit M}

/-- The construction of the class of a bundle gerbe in `H²(M, ℂ×)` (Murray, Stevenson, *Bundle gerbes:
stable isomorphism and local theory*, arXiv:math/9908135v1, §2, p.3): `a` is the class of a cocycle
`g` obtained from an open cover `{U_α}`, smooth sections `s_α : U_α → Y` of `π`, and smooth maps
`σ_αβ : U_α ∩ U_β → P` over `(s_α, s_β)`, by `σ_αβ σ_βγ = σ_αγ g_αβγ`.

**Formalization Note.** Any cover carrying such `s_α`, `σ_αβ` is allowed, not only one with contractible
intersections: p.3 uses contractibility only to make the `σ_αβ` exist, and `dd_cocycle_class` says that
the class does not depend on the choice. The cover is a set of open sets, so an index has one open set;
an indexed cover with sections restricts to such a cover. `ℂˣ` is commutative, so `σ_αγ g_αβγ` is
written `g_αβγ • σ_αγ`. -/
def IsDDCocycle (P : BundleGerbe S) (a : H2Cx M) : Prop :=
  ∃ (𝒰 : Cover M) (s : ∀ α : 𝒰.1, α.1 → S.Y) (σ : ∀ α β : 𝒰.1, ↥(α.1 ⊓ β.1) → P.bdl.P)
    (g : Cocycle (smoothUnits M) 𝒰 2),
    (∀ α, DSmooth (s α)) ∧
    (∀ α (x : α.1), S.π (s α x) = x) ∧
    (∀ α β, DSmooth (σ α β)) ∧
    (∀ (α β : 𝒰.1) (x : ↥(α.1 ⊓ β.1)), P.bdl.src (σ α β x) = s α ⟨x.1, x.2.1⟩) ∧
    (∀ (α β : 𝒰.1) (x : ↥(α.1 ⊓ β.1)), P.bdl.tgt (σ α β x) = s β ⟨x.1, x.2.2⟩) ∧
    (∀ (i : Fin 3 → 𝒰.1) (x : inter i) (hm : _),
      P.mul (σ (i 0) (i 1) ⟨x.1, mem_of_mem_inter x.2 0, mem_of_mem_inter x.2 1⟩)
          (σ (i 1) (i 2) ⟨x.1, mem_of_mem_inter x.2 1, mem_of_mem_inter x.2 2⟩) hm =
        unitsVal (g.1 i) x • σ (i 0) (i 2) ⟨x.1, mem_of_mem_inter x.2 0, mem_of_mem_inter x.2 2⟩) ∧
    cechClass (smoothUnits M) g = a

/-- `c` is the **Dixmier-Douady class** `d(P) ∈ H³(M, ℤ)` of the bundle gerbe `P` (arXiv:math/9908135v1,
§2, p.3): the image in `H³(M, ℤ)`, under `H²(M, ℂ×) ≃ H³(M, ℤ)`, of the class of `g_αβγ`.

**Formalization Note.** A relation rather than a function: that `d` is well defined is a theorem,
`dd_cocycle_class` with `exp_boundary_equiv`, and a definition must be complete without it. Defining `d`
by `Classical.choose` over an unproved existence would give a junk value until they are proved. -/
def IsDixmierDouady (P : BundleGerbe S) (c : H3 M) : Prop :=
  ∃ a : H2Cx M, IsDDCocycle P a ∧ IsExpBoundary a c

end BundleGerbeStable



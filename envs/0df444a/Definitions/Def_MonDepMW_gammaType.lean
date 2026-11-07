-- Prove2me | Definitions.Def_MonDepMW_gammaType
-- name    : MonDepMW_gammaType
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T10:47:52.890944+00:00
-- url     : https://prove2.me/theorems/a9d034e5-9361-4db1-a36a-56b6bed32388
-- title:
--   $\Gamma$-types $\mathcal T_\Gamma(G,B)$
-- statement:
--   For a finite set $\Gamma$ of first-order formulas $\varphi(x,y)$ over colored graphs, a colored graph $G$ and a set $B\subseteq V(G)$, the partition $\mathcal T_\Gamma(G,B)$ puts $u,v$ in the same part iff for every $b\in B$ and $\varphi\in\Gamma$, $\varphi(u,b)\Leftrightarrow\varphi(v,b)$ holds in $G$.
--
--   This generalizes 1-types to arbitrary formulas; its growth is bounded in Lemma 5.3.
-- source:
--   Dreier, Mählmann, Pilipczuk, Toruńczyk, Monadically Dependent Graph Classes Have Almost Bounded Merge-Width, arXiv:2611.06804 (held version, sha256 6e4b0608…), §5.1, p.18

import Mathlib
import Definitions.Def_MonDepMW_coloredGraph

set_option autoImplicit false

namespace MonDepMW

/-- **The partition `𝒯_Γ(G⁺, B)` into `Γ`-types.** Dreier, Mählmann, Pilipczuk, Toruńczyk, *Monadically Dependent Graph Classes Have Almost Bounded Merge-Width*, arXiv:2611.06804 (held version, sha256 6e4b0608…), §5.1, p.18: "For a finite set Γ of first-order formulas φ(x, y)
over colored graphs, a colored graph G, and a set B ⊆ V (G), let 𝒯Γ(G, B) denote the partition of V (G) into Γ-types
over B: vertices u, v belong to the same part if and only if, for every b ∈ B and φ ∈ Γ, we have that φ(u, b) ⇔ φ(v, b)
holds in G." -/
def gammaType {k n : ℕ} (Γ : Finset ((coloredGraph k).Formula (Fin 2))) (G : SimpleGraph (Fin n))
    (c : Fin k → Set (Fin n)) (B : Finset (Fin n)) : Setoid (Fin n) where
  r u v := ∀ b ∈ B, ∀ φ ∈ Γ, (Holds φ G c u b ↔ Holds φ G c v b)
  iseqv :=
    { refl := fun _ _ _ _ _ => Iff.rfl
      symm := fun h b hb φ hφ => (h b hb φ hφ).symm
      trans := fun h h' b hb φ hφ => (h b hb φ hφ).trans (h' b hb φ hφ) }

end MonDepMW



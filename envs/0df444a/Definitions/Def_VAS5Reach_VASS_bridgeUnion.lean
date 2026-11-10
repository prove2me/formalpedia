-- Prove2me | Definitions.Def_VAS5Reach_VASS_bridgeUnion
-- name    : VAS5Reach_VASS_bridgeUnion
-- status  : Definition
-- author  : @iris
-- created : 2026-11-09T22:27:28.400002+00:00
-- url     : https://prove2.me/theorems/5fdf4246-6584-4e32-beec-75d1e19deb58
-- title:
--   Two disjoint VASS joined by a zero-effect bridge (Case I of Theorem 6.1)
-- statement:
--   For VASS $V_1$, $V_2$ of the same dimension and states $r_1$ of $V_1$, $r_2$ of $V_2$, this is the VASS on the disjoint union of their states whose transitions are those of $V_1$, those of $V_2$, and the single zero-effect transition $(r_1, 0, r_2)$ from the first to the second. In Case I of Theorem 6.1, $V' $ is this VASS for $V_1 = \widehat{[\![V'']\!]}_{I_1,B}$ and $V_2 = \widehat{[\![V'']\!]}_{I_2,B}$, the bridge being $(r_1(u_1), 0, r_2(u_2))$.
--
--   **Formalization Note** The state set also lists $r_1$ and $r_2$, which changes nothing when they are states of $V_1$ and $V_2$, as every use requires.
-- source:
--   Chen, Fu, Fu, Reachability in Five-Dimensional Vector Addition Systems Is PSPACE-Complete, arXiv:2610.40012 (held version, sha256 a74d76f9…), Theorem 6.1 I, p.25 (PDF p.27); proof of Proposition 6.2, p.26 (PDF p.28)

import Mathlib
import Definitions.Def_VAS5Reach_VASS

namespace VAS5Reach

namespace VASS

variable {S₁ S₂ ι : Type}

open Classical in
/-- Two VASS `V₁`, `V₂` of the same dimension with disjoint state sets (the disjoint union of their
state types) connected by one zero-effect transition `(r₁, 0, r₂)` from the state `r₁` of the first
to the state `r₂` of the second. This is the shape of the VASS `V′` of Case I of Theorem 6.1, with
`V₁ = [[V″]]^_{I₁,B}` and `V₂ = [[V″]]^_{I₂,B}`.

Source: W. Chen, B. Fu, Y. Fu, *Reachability in Five-Dimensional Vector Addition Systems Is
PSPACE-Complete*, arXiv:2610.40012 (held version, sha256 a74d76f9…), Theorem 6.1 I, printed p. 25
(PDF p. 27): "V′ consists of two disjoint 5-VASS [[V″]]^_{I1,B}, [[V″]]^_{I2,B}, connected by a
zero-effect transition from the first to the second."; proof of Proposition 6.2, printed p. 26
(PDF p. 28): "Write (r1(u1), 0, r2(u2)) for the zero-effect bridge".

**Formalization Note** The state set also contains `r₁` and `r₂`, so that the bridge connects
states; when `r₁ ∈ V₁.states` and `r₂ ∈ V₂.states`, as required wherever it is used, it is exactly
the disjoint union of the two state sets. -/
noncomputable def bridgeUnion (V₁ : VASS S₁ ι) (V₂ : VASS S₂ ι) (r₁ : S₁) (r₂ : S₂) :
    VASS (S₁ ⊕ S₂) ι where
  states := V₁.states.image Sum.inl ∪ V₂.states.image Sum.inr ∪ {Sum.inl r₁, Sum.inr r₂}
  trans := V₁.trans.image (fun τ => (Sum.inl τ.1, τ.2.1, Sum.inl τ.2.2)) ∪
    V₂.trans.image (fun τ => (Sum.inr τ.1, τ.2.1, Sum.inr τ.2.2)) ∪ {(Sum.inl r₁, 0, Sum.inr r₂)}
  trans_mem := by
    intro τ h
    simp only [Finset.mem_union, Finset.mem_image, Finset.mem_insert,
      Finset.mem_singleton] at h ⊢
    rcases h with (⟨σ, hσ, rfl⟩ | ⟨σ, hσ, rfl⟩) | rfl
    · exact ⟨Or.inl (Or.inl ⟨σ.1, (V₁.trans_mem σ hσ).1, rfl⟩),
        Or.inl (Or.inl ⟨σ.2.2, (V₁.trans_mem σ hσ).2, rfl⟩)⟩
    · exact ⟨Or.inl (Or.inr ⟨σ.1, (V₂.trans_mem σ hσ).1, rfl⟩),
        Or.inl (Or.inr ⟨σ.2.2, (V₂.trans_mem σ hσ).2, rfl⟩)⟩
    · exact ⟨Or.inr (Or.inl rfl), Or.inr (Or.inr rfl)⟩

end VASS

end VAS5Reach



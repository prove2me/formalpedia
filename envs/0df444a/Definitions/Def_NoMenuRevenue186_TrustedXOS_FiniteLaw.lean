-- Prove2me | Definitions.Def_NoMenuRevenue186_TrustedXOS_FiniteLaw
-- name    : NoMenuRevenue186_TrustedXOS_FiniteLaw
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-10T07:54:36.856512+00:00
-- url     : https://prove2.me/theorems/a16078b8-840a-469e-9e55-0fbbe5b2b6d4
-- title:
--   Finite probability laws and finite expectations
-- statement:
--   A finite probability law on a type $A$ is a probability mass function $p$ with finite support. Laws are identified by their actual mass functions; support certificates contain no additional data. Its expectation is the finite weighted sum
--
--   $$\mathbb E_p[f]=\sum_{a\in\operatorname{supp}(p)}p(a)f(a).$$
--
--   The interface provides point masses, pushforwards, mixtures by finite kernels, and the uniform law on a nonempty finite set. Uniform sampling on an empty set uses an explicit fallback point mass. The parameter conditions in the hard construction make every sampling set used there nonempty; the fallback does not represent an empty conditional distribution.
--
--   This wrapper over probability mass functions makes all inner and outer expectations finite sums and ensures that a seller receives a canonical prior rather than a sampling seed.
-- source:
--   Aggarwal, Dang, Rubinstein, Zhao, STOC 2027 submission #186 (October 2026), printed p.8, PDF p.10, Section 2.1

import Mathlib

namespace NoMenuRevenue186.TrustedXOS

/-- Canonical finitely supported probability law. Only the mass function is data;
    the finiteness certificate carries no information. Section 2.1, printed p.8. -/
structure FiniteLaw (α : Type) where
  law : PMF α
  finite_support : law.support.Finite

namespace FiniteLaw

variable {α β : Type}

noncomputable def support (p : FiniteLaw α) : Finset α := p.finite_support.toFinset

noncomputable def expect (p : FiniteLaw α) (f : α → ℝ) : ℝ :=
  ∑ a ∈ p.support, (p.law a).toReal * f a

noncomputable def pure (a : α) : FiniteLaw α :=
  ⟨PMF.pure a, by simp⟩

noncomputable def map (p : FiniteLaw α) (f : α → β) : FiniteLaw β :=
  ⟨p.law.map f, by rw [PMF.support_map]; exact p.finite_support.image f⟩

noncomputable def bind (p : FiniteLaw α) (f : α → FiniteLaw β) : FiniteLaw β :=
  ⟨p.law.bind (fun a => (f a).law), by
    rw [PMF.support_bind]
    exact p.finite_support.biUnion (fun a _ => (f a).finite_support)⟩

/-- The fallback is used only for an empty sampling set. Every construction theorem
    states the parameters that make its sampling sets nonempty. -/
noncomputable def uniform (s : Finset α) (fallback : α) : FiniteLaw α := by
  classical
  exact if hs : s.Nonempty then
    ⟨PMF.uniformOfFinset s hs, by rw [PMF.support_uniformOfFinset]; exact s.finite_toSet⟩
  else pure fallback

end FiniteLaw
end NoMenuRevenue186.TrustedXOS



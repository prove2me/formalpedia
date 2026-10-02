-- Prove2me | Definitions.Def_LeblSCV_Varieties_vanishingIdeal
-- name    : LeblSCV_Varieties_vanishingIdeal
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-09-28T10:12:06.617679+00:00
-- url     : https://prove2.me/theorems/a56ac3ec-c1f4-4b2f-9952-3177150323af
-- title:
--   The ideal $I_p(X)$ of germs vanishing on $(X,p)$ (p. 183)
-- statement:
--   Let $p \in \mathbb{C}^n$ and $X \subset \mathbb{C}^n$. For a germ $(f, p) \in \mathcal{O}_p$, the germ $(Z_f, p)$ is the germ at $p$ of the zero set $Z_f = f^{-1}(0)$ of a representative. The **ideal of $X$ at $p$** is
--   $$I_p(X) = \{ (f, p) \in \mathcal{O}_p : (X, p) \subset (Z_f, p) \},$$
--   the germs of holomorphic functions vanishing on $X$ near $p$. It is an ideal of $\mathcal{O}_p$ and depends only on the germ $(X, p)$.
--
--   **Formalization Note.** An `Ideal` of the subring `holGerms p`. A germ belongs to it if some representative $f$ (a function $\mathbb{C}^n \to \mathbb{C}$ with the given germ) satisfies $X \cap W \subset f^{-1}(0) \cap W$ for a neighborhood $W$ of $p$; representatives with the same germ agree near $p$, so the choice does not matter.
-- source:
--   Lebl, Tasty Bits of Several Complex Variables, version 4.4 (2026), p. 183 (display defining I_p(X))

import Mathlib
import Definitions.Def_LeblSCV_Varieties_holGerms

namespace LeblSCV.Varieties

open Filter Topology

/-- Lebl, p. 183: `I_p(X) = {(f, p) ∈ 𝒪_p : (X, p) ⊂ (Z_f, p)}`, the ideal of germs at `p` of
holomorphic functions vanishing on `X` near `p`: a germ belongs to it if some representative `f`
satisfies `X ∩ W ⊆ Z_f ∩ W = f⁻¹(0) ∩ W` for a neighborhood `W` of `p` (Definition 6.1.3).
(Germ-equal representatives agree near `p`, so the choice of representative is immaterial.) -/
def vanishingIdeal {n : ℕ} (p : Fin n → ℂ) (X : Set (Fin n → ℂ)) : Ideal (holGerms p) where
  carrier := {g | ∃ f : (Fin n → ℂ) → ℂ, (g : Germ (𝓝 p) ℂ) = (f : Germ (𝓝 p) ℂ) ∧
    ∃ W ∈ 𝓝 p, X ∩ W ⊆ f ⁻¹' {0} ∩ W}
  add_mem' := by
    rintro a b ⟨f, hfa, W, hW, hXW⟩ ⟨f', hfb, W', hW', hXW'⟩
    refine ⟨f + f', ?_, W ∩ W', Filter.inter_mem hW hW', ?_⟩
    · simp only [Subring.coe_add, hfa, hfb, Germ.coe_add]
    · rintro z ⟨hzX, hzW, hzW'⟩
      have h1 := (hXW ⟨hzX, hzW⟩).1
      have h2 := (hXW' ⟨hzX, hzW'⟩).1
      simp only [Set.mem_preimage, Set.mem_singleton_iff] at h1 h2
      exact ⟨by simp [h1, h2], hzW, hzW'⟩
  zero_mem' := ⟨fun _ => 0, rfl, Set.univ, Filter.univ_mem, fun z hz => ⟨rfl, hz.2⟩⟩
  smul_mem' := by
    rintro c b ⟨f, hfb, W, hW, hXW⟩
    obtain ⟨h, V, -, -, -, hc⟩ := c.2
    refine ⟨h * f, ?_, W, hW, ?_⟩
    · simp only [smul_eq_mul, Subring.coe_mul, hfb, hc, Germ.coe_mul]
    · rintro z ⟨hzX, hzW⟩
      have h1 := (hXW ⟨hzX, hzW⟩).1
      simp only [Set.mem_preimage, Set.mem_singleton_iff] at h1
      exact ⟨by simp [h1], hzW⟩

end LeblSCV.Varieties



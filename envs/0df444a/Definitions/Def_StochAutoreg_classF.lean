-- Prove2me | Definitions.Def_StochAutoreg_classF
-- name    : StochAutoreg_classF
-- status  : Definition
-- author  : @iris
-- created : 2026-11-07T02:22:43.753801+00:00
-- url     : https://prove2.me/theorems/48c6cef2-bfa6-4d69-9098-81c2089ae3fd
-- title:
--   The combined class $\mathcal F=\{g\oplus h_0\}\cup\{g_0\oplus h\}$
-- statement:
--   For a fixed $g_0=g_{\omega_0,\tau_0}\in G_N$,
--
--   $$\mathcal F=\{g\oplus h_0:g\in G_N\}\cup\{g_0\oplus h:h\in H_D\},$$
--
--   where all roots are placed together, $\oplus$ uses the first generator on its root trees and the second on its disjoint root trees, and the common transitions of Lemma 6.1 apply elsewhere. It is not the full product $G_N\times H_D$.
--
--   **Formalization Note** The second set ranges over the active members of $H_D$; $g_0\oplus h_0$ is already in the first.
-- source:
--   Doron-Arad–Mehalel–Mossel, Stochastic Autoregressive Learning, arXiv:2608.07224, proof of Theorem 7.1, p.16

import Mathlib
import Definitions.Def_StochAutoreg_isolate
import Definitions.Def_StochAutoreg_gRule
import Definitions.Def_StochAutoreg_hRuleOff
import Definitions.Def_StochAutoreg_hRuleOn

namespace StochAutoreg

/-- The combined class `F = {g ⊕ h₀ : g ∈ G_N} ∪ {g₀ ⊕ h : h ∈ H_D}`, with `g₀ = g_{ω₀,τ₀}`, all roots being placed by one
application of Lemma 6.1. Doron-Arad–Mehalel–Mossel, *Stochastic Autoregressive Learning*, arXiv:2608.07224, proof of Theorem 7.1, p.16.

**Formalization Note.** The union is over `h ∈ H_D`, whose inactive member gives `g₀ ⊕ h₀`, already in the first set; the
second set ranges over the active `h_{b,s}` only. `F` is not the full product `G_N × H_D`. -/
def classF (J M : ℕ) (ε tG tH : ℝ) (N D : ℕ) (ω₀ : Fin N → ℤˣ) (τ₀ : ℤˣ)
    (b : (Fin N ⊕ Unit) ⊕ Fin (D + 1) → List Bool) : Set Generator :=
  (Set.range fun p : (Fin N → ℤˣ) × ℤˣ =>
      isolate M b (Sum.elim (gRule J M ε tG p.1 p.2) (hRuleOff D))) ∪
    Set.range fun p : Bool × (Fin D → ℤˣ) =>
      isolate M b (Sum.elim (gRule J M ε tG ω₀ τ₀) (hRuleOn J M tH p.1 p.2))

end StochAutoreg



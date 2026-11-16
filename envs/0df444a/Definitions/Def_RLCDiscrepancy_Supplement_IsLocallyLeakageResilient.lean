-- Prove2me | Definitions.Def_RLCDiscrepancy_Supplement_IsLocallyLeakageResilient
-- name    : RLCDiscrepancy_Supplement_IsLocallyLeakageResilient
-- status  : Definition
-- author  : @iris
-- created : 2026-11-16T03:50:05.409186+00:00
-- url     : https://prove2.me/theorems/b28a42c1-f1eb-4301-98a2-75ad237ea7b9
-- title:
--   $(n,t_{\mathrm{rec}},t_{\mathrm{priv}},\varepsilon)$-locally leakage-resilient ramp scheme
-- statement:
--   A secret sharing scheme $(\mathrm{Share},\mathrm{Rec})$ with secrets and shares in $\mathbb F_q$ is **$(n,t_{\mathrm{rec}},t_{\mathrm{priv}},\varepsilon)$-locally leakage-resilient** if it is an $(n,t_{\mathrm{rec}},t_{\mathrm{priv}})$-ramp scheme and, for every family of possibly distinct 1-bit leakage functions $g_1,\dots,g_n:\mathbb F_q\to\{0,1\}$ and all secrets $s,s'$,
--   $$
--   \mathrm{SD}\big(g(\mathrm{Share}(s)),\,g(\mathrm{Share}(s'))\big)\le\varepsilon,\qquad g(S)=(g_1(S_1),\dots,g_n(S_n)).
--   $$
--   This is the security notion of Theorems 6.5 and 6.14.
--
--   **Formalization Note** $\{0,1\}$ is `Bool`; the $g_i$ are arbitrary maps.
-- source:
--   Doron, Leonov, Mosheiff, Navas, Resch, Ribeiro, Discrepancy for Random Linear Codes, arXiv:2606.24471 (PDF sha256 f03561c3…), Definition 6.4 and §6.1, p.46

import Mathlib
import Definitions.Def_PunctSketch_coinProb
import Definitions.Def_RLCDiscrepancy_Supplement_statDist
import Definitions.Def_RLCDiscrepancy_Supplement_RampScheme

namespace RLCDiscrepancy.Supplement

/-- **(n, t_rec, t_priv, ε)-locally leakage-resilient ramp secret sharing scheme**
(Definition 6.4 with the 1-bit local leakage family, p.46). Doron, Leonov, Mosheiff, Navas, Resch, Ribeiro, *Discrepancy for Random Linear Codes*,
arXiv:2606.24471 (PDF sha256 f03561c3…), Definition 6.4 and §6.1, p.46:
"An (n, t_rec, t_priv, G, ε)-leakage-resilient ramp secret sharing scheme is an
(n, t_rec, t_priv)-ramp secret sharing scheme with the following additional property:
Leakage-resilience against G: For any leakage function g ∈ G and any two secrets s, s′ ∈ S with
corresponding shares S = Share(s) and S′ = Share(s′), we have g(S) ≈_ε g(S′)." The family G contains
"all functions g = (g_1, …, g_n) of the form g(S) = (g_1(S_1), …, g_n(S_n)), for possibly distinct
bounded-output functions g_i : F_q → {0, 1}", and such schemes are called "(n, t_rec, t_priv, ε)-locally
leakage-resilient".

**Formalization Note.** {0, 1} is `Bool`; g is a family `Fin n → F → Bool` of arbitrary maps;
g(S) ≈_ε g(S′) is `statDist ≤ ε` (Definition 6.3) with uniform coins on `Ω`. -/
def IsLocallyLeakageResilient {F : Type*} [Fintype F] {n : ℕ} {Ω : Type*} [Fintype Ω]
    (P : RampScheme F n Ω) (tRec tPriv : ℕ) (ε : ℝ) : Prop :=
  P.IsRamp tRec tPriv ∧
  ∀ (g : Fin n → F → Bool) (s s' : F),
    statDist (fun ω i => g i (P.share s ω i)) (fun ω i => g i (P.share s' ω i)) ≤ ε

end RLCDiscrepancy.Supplement



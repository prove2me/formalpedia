-- Prove2me | Definitions.Def_KarpLiptonOM_PiP
-- name    : KarpLiptonOM_PiP
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T06:40:39.688289+00:00
-- url     : https://prove2.me/theorems/b87f78ae-3590-4e51-b562-18abecb5efc4
-- title:
--   $\Pi^{\mathrm P}_k = \mathrm{co}\Sigma^{\mathrm P}_k$
-- statement:
--   $\Pi^{\mathrm P}_k$ is the class of complements of languages in $\Sigma^{\mathrm P}_k$: $L \in \Pi^{\mathrm P}_k$ iff $\overline L \in \Sigma^{\mathrm P}_k$.
-- source:
--   Hirsch–Volkovich, The Ultimate Karp–Lipton Collapse, STOC 2027 submission (manuscript sha256 aca09a2b…), §A.2.3, p.23 (standard class)

import Mathlib
import Definitions.Def_KarpLiptonOM_SigmaP

namespace KarpLiptonOM

/-- `Π_k^P = co-Σ_k^P` (Hirsch–Volkovich, *The Ultimate Karp–Lipton Collapse*, STOC 2027 submission manuscript (sha256 aca09a2b…7c62fd1b), §A.2.3, p.23, "OMIN ⊆ Σ₂^P ∩ Π₂^P"; standard). -/
def PiP (k : ℕ) : Set (Set (List Bool)) := {L | Lᶜ ∈ SigmaP k}

end KarpLiptonOM



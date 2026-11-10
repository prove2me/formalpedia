-- Prove2me | Definitions.Def_ChoiSemiHonestMPC_OTUpper_Postprocessing
-- name    : ChoiSemiHonestMPC_OTUpper_Postprocessing
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-11-10T00:30:09.605218+00:00
-- url     : https://prove2.me/theorems/03e67f9e-819d-4cbd-bcea-e096182f92a9
-- title:
--   The common postprocessing family and the complete protocol of Theorem 8.3
-- statement:
--   Theorem 8.3 uses $K=\lceil C_\alpha(\ell+\lambda)\rceil$ wROT pairs (`Kof`). A `PostFamily` assigns to every $(\ell,\lambda)$ a two-client protocol (`Protocol 0`: no servers, so no server messages and no server state). Its clients' only inputs are their outputs of the $K$ wROT pairs; its only other resource is fresh private coins; it outputs $\ell$ ROT pairs. `fullOT gen Cα post ℓ λ` is the complete protocol: the generation protocol for $K$ pairs, then `post ℓ λ`, then the three-bit conversion on the chosen inputs. Each chosen postprocessing program satisfies Synchronous, so its declared round bound really completes operations and deliveries.
-- source:
--   Choi 2026, STOC 2027 submission manuscript (sha256 3a47662a…), Section 8 (Lemma 8.1, Section 8.2) and the proof of Theorem 8.3, p. 39–44 (PDF 41–46)

import Mathlib
import Definitions.Def_ChoiSemiHonestMPC_OTUpper_Security

open scoped BigOperators ENNReal NNReal

noncomputable section

namespace ChoiSemiHonestMPC.OTUpper

/-- The number of wROT pairs generated in Theorem 8.3: `K = ⌈C_α (ℓ + λ)⌉`. -/
def Kof (Cα : ℝ) (ℓ lam : ℕ) : ℕ := ⌈Cα * ((ℓ : ℝ) + lam)⌉₊

/-- A common postprocessing family (Section 8, Stage A): for every `ℓ, λ`, a two-client
protocol (no servers, so no server messages and no server state) whose clients' only
inputs are their outputs of `K = ⌈C_α(ℓ+λ)⌉` wROT pairs (`(U0, U1)` for Alice, `(C, U_C)`
for Bob) and whose only other resource is fresh private coins; it outputs `ℓ` ROT pairs. -/
abbrev PostFamily (Cα : ℝ) : Type 1 :=
  ∀ ℓ lam : ℕ, {Q : Protocol 0 (Bits (Kof Cα ℓ lam) × Bits (Kof Cα ℓ lam))
    (Bits (Kof Cα ℓ lam) × Bits (Kof Cα ℓ lam)) (Bits ℓ × Bits ℓ) (Bits ℓ × Bits ℓ) // Q.Synchronous}

/-- The complete protocol of Theorem 8.3 for `ℓ` OTs with security parameter `λ`: the
generation protocol `gen K` for `K = ⌈C_α(ℓ+λ)⌉` wROT pairs, followed by the common
postprocessing `post ℓ λ` and the three-bit conversion (`otProtocol`). -/
def fullOT {n : ℕ} (gen : (K : ℕ) → Protocol n Unit Unit (Bits K × Bits K) (Bits K × Bits K))
    (Cα : ℝ) (post : PostFamily Cα) (ℓ lam : ℕ) :
    Protocol n (Bits ℓ × Bits ℓ) (Bits ℓ) Unit (Bits ℓ) :=
  otProtocol (gen (Kof Cα ℓ lam)) (post ℓ lam).val

end ChoiSemiHonestMPC.OTUpper



-- Prove2me | Definitions.Def_CompDesign_Supplement_IsPFBestResponse
-- name    : CompDesign_Supplement_IsPFBestResponse
-- status  : Definition
-- author  : @iris
-- created : 2026-11-15T20:50:33.814+00:00
-- url     : https://prove2.me/theorems/65f6313a-7bdd-4098-b72c-51e5e195d7e5
-- title:
--   Platform-favoring best response of the single agent (§7.1)
-- statement:
--   A single agent has actions $A=\{1,\dots,m\}$, costs $c_e$ and additive cost $c(S)=\sum_{e\in S}c_e$; the compensation rule $p:2^A\to[0,B]$ pays $p(S)$ when the agent chooses $S$. $S$ is a **platform-favoring best response** if
--   $$p(S)-c(S)\ \ge\ p(T)-c(T)\quad\text{for all }T\subseteq A,$$
--   and $v(S)\ge v(T)$ for every $T$ with $p(T)-c(T)=p(S)-c(S)$: among the payoff maximizers the agent chooses one of maximum principal value.
-- source:
--   Anagnostides, Bhawalkar, Liaw, Mehta, Paes Leme, Teng, Velegkas, Zheng, Compensation Design, arXiv:2607.14438 (version of November 3, 2026, sha256 3d305d4d…), §7.1, p.52 (PDF 55)

import Mathlib

namespace CompDesign.Supplement

/-- A platform-favoring best response of the single agent of §7.1, p.52 (PDF 55), of Anagnostides et al., *Compensation Design*, arXiv:2607.14438 (version of November 3, 2026,
sha256 3d305d4d…): the
agent with action set `A = Fin m`, additive costs `c(S) = ∑_{e∈S} c_e` and compensation rule
`p : 2^A → [0, B]` chooses `S ∈ argmax_S {p(S) − c(S)}`, and among the payoff maximizers one with
maximum principal value `v(S)`. -/
def IsPFBestResponse {m : ℕ} (p : Finset (Fin m) → ℝ) (v : Finset (Fin m) → ℝ)
    (c : Fin m → ℝ) (S : Finset (Fin m)) : Prop :=
  (∀ T, p T - ∑ e ∈ T, c e ≤ p S - ∑ e ∈ S, c e) ∧
    ∀ T, p T - ∑ e ∈ T, c e = p S - ∑ e ∈ S, c e → v T ≤ v S

end CompDesign.Supplement



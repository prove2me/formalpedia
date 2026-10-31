-- Prove2me | Definitions.Def_PersuadeFly_historyAt
-- name    : PersuadeFly_historyAt
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T04:28:13.707003+00:00
-- url     : https://prove2.me/theorems/ec65ad66-1e88-4ccd-8829-d941429897fe
-- title:
--   The history $h_t$ of a path
-- statement:
--   For a path $(\omega_\tau,a_\tau)_{\tau\in[T]}$ of states and recommendations and a time $t\in[T]$, the history $h_t$ is the sequence of its first $t$ entries $(\omega_\tau,a_\tau)_{\tau<t}$, with $h_0=\emptyset$.
--
--   **Formalization Note** $[T]=\{0,\dots,T-1\}$. The paper's history also records the receivers' actions $\hat a_\tau$; under robust persuasiveness the paper assumes $\hat a_\tau=a_\tau$ (p.19), so they are omitted.
-- source:
--   Zu, Iyer, Xu, Learning to Persuade on the Fly: Robustness Against Ignorance, arXiv:2102.10156v2, §2, p.13

import Mathlib

namespace PersuadeFly

/-- **The history `h_t` of a path.** Zu, Iyer, Xu, *Learning to Persuade on the Fly: Robustness Against Ignorance*, arXiv:2102.10156v2, §2, p.13: `h_t = ∪_{τ<t} {(τ, ω_τ, a_τ, â_τ)}`, `h₀ = ∅`.
For a path `(ω_τ, a_τ)_{τ ∈ [T]}`, `historyAt path t` is its first `t` entries.

**Formalization Note** `[T] = {0, …, T − 1}` (p.11) is `Fin T`, and a history at time `t` is a
function `Fin t → Ω × A`. The receivers' actions `â_τ` are omitted: under robust persuasiveness the
paper assumes `â_τ = a_τ` (p.19), so they carry no further information. -/
def historyAt {X : Type} {T : ℕ} (path : Fin T → X) (t : Fin T) : Fin t → X :=
  fun i => path (Fin.castLE t.isLt.le i)

end PersuadeFly



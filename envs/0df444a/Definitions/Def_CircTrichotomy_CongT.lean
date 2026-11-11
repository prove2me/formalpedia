-- Prove2me | Definitions.Def_CircTrichotomy_CongT
-- name    : CircTrichotomy_CongT
-- status  : Definition
-- author  : @iris
-- created : 2026-11-10T21:58:57.613239+00:00
-- url     : https://prove2.me/theorems/3b405b36-d6d3-444e-845b-aba951781cdf
-- title:
--   The modular threshold-counting congruence $\mathcal C^t_k$
-- statement:
--   For $k,t\ge1$ and $u,v\in\Sigma^+$, $u\,\mathcal C^t_k\,v$ if
--   $$|u|\equiv_k|v|\quad\text{and}\quad |\pi_{i,k}(u)|_a\equiv_t|\pi_{i,k}(v)|_a\ \text{ for all } a\in\Sigma,\ i\in[0,k-1],$$
--   i.e. the lengths agree modulo $k$ and, in each residue class, the number of occurrences of each letter agrees up to threshold $t$.
-- source:
--   Göller, Manuel, A Circuit Complexity Trichotomy For Regular Languages, arXiv:2611.03615 (version of November 3, 2026, sha256 5bef1791…), Definition B.2, p.21

import Mathlib
import Definitions.Def_CircTrichotomy_piMod
import Definitions.Def_CircTrichotomy_thrModEq

set_option autoImplicit false

namespace CircTrichotomy

/-- **Modular threshold-counting congruence `𝒞^t_k`** (Göller, Manuel, *A Circuit Complexity Trichotomy For Regular Languages*, arXiv:2611.03615 (version of November 3, 2026, sha256 5bef1791…), Definition B.2, p.21): "Let
k, t ∈ ℕ>0. The congruence 𝒞^t_k on Σ⁺ is defined as follows: u 𝒞^t_k v if
|u| ≡_k |v| and |π_{i,k}(u)|_a ≡_t |π_{i,k}(v)|_a   (33)
for all a ∈ Σ and i ∈ [0, k − 1]." -/
def CongT {α : Type} (k t : ℕ) (u v : List α) : Prop :=
  u.length % k = v.length % k ∧ ∀ a : α, ∀ i < k, thrEq t (cntMod k i a u) (cntMod k i a v)

end CircTrichotomy



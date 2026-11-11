-- Prove2me | Definitions.Def_CircTrichotomy_simeqTD
-- name    : CircTrichotomy_simeqTD
-- status  : Definition
-- author  : @iris
-- created : 2026-11-10T22:02:19.736507+00:00
-- url     : https://prove2.me/theorems/fba47118-175e-4527-a9aa-2788a2b82efe
-- title:
--   The congruences $\simeq^{t,d}_k$ and $\simeq_k=\simeq^{k,k}_k$
-- statement:
--   For $k,t\ge1$, $d\in\mathbb N$ and $u,v\in\Sigma^+$, $u\simeq^{t,d}_k v$ if either $\min(|u|,|v|)\le2k$ and $u=v$, or $|u|,|v|>2k$ and
--   1. $\alpha_k(u)=\alpha_k(v)$ (same prefix of length $k$),
--   2. $\omega_k(u)=\omega_k(v)$ (same suffix of length $k$),
--   3. $\kappa_k(u)\,\mathcal C^{t,d}_k\,\kappa_k(v)$ (middle factors).
--
--   The **diagonal congruence** is $\simeq_k=\simeq^{k,k}_k$. Regular languages of sublinear circuit complexity are exactly the unions of $\simeq_k$-classes.
-- source:
--   Göller, Manuel, A Circuit Complexity Trichotomy For Regular Languages, arXiv:2611.03615 (version of November 3, 2026, sha256 5bef1791…), Definitions B.8 and B.11, pp.24–25

import Mathlib
import Definitions.Def_CircTrichotomy_CongTD

set_option autoImplicit false

namespace CircTrichotomy

/-- **`≃^{t,d}_k`** (Göller, Manuel, *A Circuit Complexity Trichotomy For Regular Languages*, arXiv:2611.03615 (version of November 3, 2026, sha256 5bef1791…), Definition B.8, p.24): "For k, t ∈ ℕ>0 and d ∈ ℕ we define the binary
relation u ≃^{t,d}_k v over Σ⁺ as follows:
• either min(|u|, |v|) ≤ 2k and u = v, or
• |u|, |v| > 2k and (1) α_k(u) = α_k(v), (2) ω_k(u) = ω_k(v), (3) κ_k(u) 𝒞^{t,d}_k κ_k(v)."

`α_k` is the length-`k` prefix (`take k`), `ω_k` the length-`k` suffix (`drop (|u| − k)`), and `κ_k`
the middle factor (`kappa`). -/
def simeqTD {α : Type} (k t d : ℕ) (u v : List α) : Prop :=
  (min u.length v.length ≤ 2 * k ∧ u = v) ∨
    (2 * k < u.length ∧ 2 * k < v.length ∧ u.take k = v.take k ∧
      u.drop (u.length - k) = v.drop (v.length - k) ∧ CongTD k t d (kappa k u) (kappa k v))

/-- **Diagonal congruence `≃_k`** (Göller, Manuel, *A Circuit Complexity Trichotomy For Regular Languages*, arXiv:2611.03615 (version of November 3, 2026, sha256 5bef1791…), Definition B.11, p.25): "For all k ∈ ℕ>0 we let
≃_k = ≃^{k,k}_k." -/
def simeqK {α : Type} (k : ℕ) (u v : List α) : Prop := simeqTD k k k u v

end CircTrichotomy



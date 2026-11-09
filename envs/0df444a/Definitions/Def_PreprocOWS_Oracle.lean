-- Prove2me | Definitions.Def_PreprocOWS_Oracle
-- name    : PreprocOWS_Oracle
-- status  : Definition
-- author  : @iris
-- created : 2026-11-08T07:15:37.554269+00:00
-- url     : https://prove2.me/theorems/b489a408-49c0-4dd2-9b1e-70599280d771
-- title:
--   Random oracle $R:[K]\times[N]\to\{\pm1\}$ and the uniform average
-- statement:
--   The **random oracle** of the one-way-state (1OWS) game is a function $R:[K]\times[N]\to\{\pm1\}$. It is encoded as a Boolean function $R:\mathrm{Fin}\,K\times\mathrm{Fin}\,N\to\{\mathsf{true},\mathsf{false}\}$ together with the sign
--   $$
--   \mathrm{sgn}(b)=(-1)^{b}\in\{\pm1\}\subset\mathbb C,\qquad \mathrm{sgn}(\mathsf{true})=-1,\ \mathrm{sgn}(\mathsf{false})=1,
--   $$
--   so that $R(p)=\mathrm{sgn}(R\,p)$. "$R$ is sampled" means $R$ is uniform over all $2^{KN}$ such functions. For a function $f$ on a finite set $\alpha$ the **uniform average** is
--   $$
--   \mathbb E_{a}f(a)=\frac1{|\alpha|}\sum_{a\in\alpha}f(a),
--   $$
--   used both for $\mathbb E_R$ (over all oracles) and for $\mathbb E_k$ (over keys).
--
--   These are the probability-theoretic primitives of the quantum random oracle model used throughout the mission.
--
--   **Formalization Note** The index sets $[K]=\{1,\dots,K\}$ and $[N]$ are relabelled $0$-based. The average is defined for real- or complex-valued $f$; on an empty set it is $0$, and every use averages over a nonempty set.
-- source:
--   Dong, Lombardi, Lower Bounds for Preprocessing Attacks on Quantum Cryptography, arXiv:2610.02101 (version of 2026-11-02, sha256 7a0bd8da…), Definition 5.1, p.16 (PDF p.19); §5.1, p.17 (PDF p.20)

import Mathlib
open Matrix

namespace PreprocOWS

/-- The **random oracle** `R : [K] × [N] → {±1}` of the 1OWS security game, Dong–Lombardi,
*Lower Bounds for Preprocessing Attacks on Quantum Cryptography*, arXiv:2610.02101 (version of
2026-11-02, sha256 7a0bd8da…), Definition 5.1, p.16 (PDF p.19).

**Formalization Note.** `R` is encoded as a Boolean function on `Fin K × Fin N`; the sign `R(p) ∈ {±1}`
is `sgn (R p)`, with `true ↦ −1` and `false ↦ +1`. The index sets `[K] = {1,…,K}` and `[N]` are
relabelled `0`-based as `Fin K`, `Fin N`. "R is sampled" means the uniform distribution over all
`2^{KN}` such functions, taken by `avg`. -/
abbrev Oracle (K N : ℕ) : Type := Fin K × Fin N → Bool

/-- The sign `(-1)^b ∈ {±1} ⊂ ℂ` of a bit: `sgn true = −1`, `sgn false = 1` (arXiv:2610.02101,
Definition 5.1, p.16: `R` takes values in `{±1}`). -/
def sgn (b : Bool) : ℂ := if b then -1 else 1

/-- The **uniform average** `E_a f(a) = |α|⁻¹ ∑_a f(a)` over a finite type, used for `E_R` (uniform
over all oracles) and `E_k` (uniform over keys) in arXiv:2610.02101, §5.1, p.17 (PDF p.20).

**Formalization Note.** It is defined for real- or complex-valued `f` (any real vector space). On an
empty type it is `0`; every use in this mission averages over a nonempty type. -/
noncomputable def avg {α M : Type*} [Fintype α] [AddCommGroup M] [Module ℝ M] (f : α → M) : M :=
  (Fintype.card α : ℝ)⁻¹ • ∑ a, f a

end PreprocOWS



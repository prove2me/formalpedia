-- Prove2me | Definitions.Def_StochAutoreg_Generator
-- name    : StochAutoreg_Generator
-- status  : Definition
-- author  : @iris
-- created : 2026-11-07T02:11:26.401199+00:00
-- url     : https://prove2.me/theorems/2e88735b-26a0-44f4-a15e-5dd146ff7f49
-- title:
--   Stochastic next-token generator $g:\Sigma^\star\to\Delta(\Sigma)$
-- statement:
--   A **stochastic next-token generator** on the binary alphabet $\Sigma=\{0,1\}$ assigns to every string $s\in\Sigma^\star$ a law on $\{0,1\}$. A law on $\{0,1\}$ is its mass at $1$, so a generator is a map $g:\Sigma^\star\to[0,1]$ and $g(s)$ is the one-step probability $p_g(s)=g(s)(1)$. A **generator class** is a set $\mathcal F$ of generators.
--
--   **Formalization Note** A string is a list of booleans, oldest token first, and `true` is the token $1$.
-- source:
--   Doron-Arad–Mehalel–Mossel, Stochastic Autoregressive Learning, arXiv:2608.07224, §1.1, p.2

import Mathlib

namespace StochAutoreg

/-- A **stochastic next-token generator** `g : Σ⋆ → Δ(Σ)` on the binary alphabet `Σ = {0,1}`.
Doron-Arad–Mehalel–Mossel, *Stochastic Autoregressive Learning*, arXiv:2608.07224, §1.1, p.2.

**Formalization Note.** A prompt or state in `Σ⋆` is a `List Bool`, oldest token first, with `true`
for the token `1`. A law on `{0,1}` is represented by its mass at `1`, so `g s` is the paper's
one-step probability `p_g(s) = g(s)(1)`. -/
abbrev Generator : Type := List Bool → unitInterval

end StochAutoreg



-- Prove2me | Definitions.Def_KellyStochasticNetworks_Erlang
-- name    : KellyStochasticNetworks_Erlang
-- status  : Definition
-- author  : @naimengye
-- created : 2026-09-18T05:45:32.248096+00:00
-- url     : https://prove2.me/theorems/4402acbb-5a65-4c5f-9846-d1b0f011e829
-- title:
--   Erlang's formula $E(\nu,C)$ and the rates of the loss link
-- statement:
--   The model of section 1.3 of Kelly and Yudovina, *Stochastic Networks*: a single telephone
--   link with $C$ parallel circuits and no waiting room.
--
--   Calls arrive as a Poisson process of rate $\lambda$. Each call holds one circuit for an
--   exponentially distributed time of parameter $\mu$, independently of the other calls and of the
--   arrival process. A call that finds all $C$ circuits busy is lost. Writing $X(t)$ for the
--   number of busy circuits, $X$ is a Markov process on $\{0,1,\dots,C\}$ with transition rates
--   $$q(j,j+1) = \lambda \quad (j = 0,1,\dots,C-1), \qquad q(j,j-1) = j\mu \quad (j = 1,2,\dots,C),$$
--   every other rate, including $q(j,j)$, being zero. The upward rate is the Poisson arrival
--   assumption; the downward rate $j\mu$ is the rate at which the first of $j$ ongoing calls
--   finishes.
--
--   **Erlang's formula** is
--   $$E(\nu, C) = \frac{\nu^{C}/C!}{\sum_{j=0}^{C} \nu^{j}/j!},$$
--   equation (1.5) of the book, where $\nu$ is the traffic intensity. Its role is that
--   $E(\lambda/\mu, C)$ is the equilibrium probability that all $C$ circuits are busy, and hence
--   the probability that an arriving call is lost.
--
--   **Formalization Note** The state space is `Fin (C + 1)`, so the state is the number of busy
--   circuits and the boundaries $0$ and $C$ are enforced by the type. The rate matrix is written
--   as a nested conditional on the integer values of the two indices, which makes `q j j = 0`
--   automatic.
-- source:
--   Kelly & Yudovina, Stochastic Networks, CUP 2014, ch. 1 section 1.3, pp. 18-19 (PDF pp. 26-27); the transition rates displayed on p. 18 and Erlang's formula, equation (1.5), on p. 19. sha256 ec271d555059aee58613e5e9a98b8346214b16185c527314f5d94c1ac8b17b6a

import Mathlib

namespace KellyStochasticNetworks

/-- **Erlang's formula.** For a traffic intensity `ν` and `C` circuits,
`E(ν, C) = (ν ^ C / C !) / ∑ j ≤ C, ν ^ j / j !`.
This is equation (1.5) of Kelly–Yudovina, *Stochastic Networks*. -/
noncomputable def erlang (ν : ℝ) (C : ℕ) : ℝ :=
  (ν ^ C / (Nat.factorial C : ℝ)) /
    ∑ j ∈ Finset.range (C + 1), ν ^ j / (Nat.factorial j : ℝ)

/-- **The transition rates of the Erlang loss link** with `C` parallel circuits, calls arriving
as a Poisson process of rate `lam` and call holding times exponential of parameter `mu`.
The state is the number of busy circuits, so `q j (j+1) = lam` for `j < C`,
`q j (j-1) = j * mu` for `j ≥ 1`, and every other rate — including `q j j` — is zero.
These are the rates displayed on p. 18 of Kelly–Yudovina, *Stochastic Networks*. -/
noncomputable def erlangRates (lam mu : ℝ) (C : ℕ) : Fin (C + 1) → Fin (C + 1) → ℝ :=
  fun j k =>
    if (k : ℕ) = (j : ℕ) + 1 then lam
    else if (j : ℕ) = (k : ℕ) + 1 then ((j : ℕ) : ℝ) * mu
    else 0

end KellyStochasticNetworks



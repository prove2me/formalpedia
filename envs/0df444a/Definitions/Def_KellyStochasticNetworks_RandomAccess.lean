-- Prove2me | Definitions.Def_KellyStochasticNetworks_RandomAccess
-- name    : KellyStochasticNetworks_RandomAccess
-- status  : Definition
-- author  : @naimengye
-- created : 2026-09-18T16:09:51.406722+00:00
-- url     : https://prove2.me/theorems/1019676d-c6a1-40a3-bcc9-459189daf1c5
-- title:
--   Random access: the ALOHA slot probabilities and the critical rate of a backoff scheme
-- statement:
--   The random access model of Chapter 5 of Kelly and Yudovina, *Stochastic Networks*.
--
--   Time is slotted and a transmission attempt occupies one slot. New packets arrive in a Poisson
--   stream of rate $\nu$. A slot with exactly one attempt carries its packet; a slot with two or
--   more is a collision and carries nothing.
--
--   **ALOHA.** After an unsuccessful attempt a station retransmits with probability $f$ in each
--   following slot. With a backlog of $n$ packets awaiting retransmission, exactly one
--   transmission is attempted with probability
--   $$e^{-\nu}\,n f (1-f)^{n-1} \;+\; \nu e^{-\nu}(1-f)^{n},$$
--   the two terms being "no new packet and exactly one retransmission" and "one new packet and no
--   retransmission". In the proof of Proposition 5.3, $p(n)$ denotes the probability that the
--   channel unjams before the backlog increases, given backlog $n$:
--   $$p(n)=\frac{e^{-\nu}(1+\nu)(1-f)^{n}+e^{-\nu}n f(1-f)^{n-1}}
--               {1-e^{-\nu}\bigl(1-(1-f)^{n}-nf(1-f)^{n-1}\bigr)} .$$
--
--   **Acknowledgement-based schemes.** A station learns nothing about the channel except whether
--   its own transmissions succeeded. A packet attempts transmission $x$ slots after arrival with
--   probability $h(x)$, independently across packets, with $h(1)=1$. On a channel externally
--   jammed from time $0$, every retransmission occurs, the number of attempts in slot $t$ is
--   Poisson with mean $\nu\sum_{r=1}^{t}h(r)$, and the probability that fewer than two attempts are
--   made in slot $t$ is
--   $$P_t=\Bigl(1+\nu\sum_{r=1}^{t}h(r)\Bigr)\exp\Bigl(-\nu\sum_{r=1}^{t}h(r)\Bigr).$$
--   The expected number of such slots is $H(\nu)=\sum_{t\ge1}P_t$, and the **critical rate** is
--   $\nu_c=\inf\{\nu : H(\nu)<\infty\}$. ALOHA is the scheme with $h(x)=f$ for every $x>1$.
--
--   **Formalization Note** The retransmission function is any real sequence; non-negativity and
--   the normalization $h(1)=1$ are imposed as hypotheses where a statement needs them rather than
--   built in, so that comparison schemes are expressible. The probabilities $P_t$, $p(n)$ and the
--   ALOHA success probability are defined by their closed forms, as the book displays them; the
--   Poisson and binomial derivations behind those forms are not part of the definitions.
-- source:
--   Kelly & Yudovina, Stochastic Networks, CUP 2014, ch. 5, pp. 109-123 (PDF pp. 117-131): the ALOHA protocol and the success probability P(Z_t = 1 | N_t = n) pp. 109-110, the unjamming probability p(n) in the proof of Proposition 5.3 p. 111, the acknowledgement-based model and the retransmission function h pp. 119-120, and P_t, H(nu) and nu_c p. 120. sha256 ec271d555059aee58613e5e9a98b8346214b16185c527314f5d94c1ac8b17b6a

import Mathlib

namespace KellyStochasticNetworks

/-- `ackAttemptRate h t = h(1) + ⋯ + h(t)`.  In an acknowledgement-based scheme, `h x` is the
probability that a packet attempts transmission `x` slots after its arrival (`h 1 = 1`), and on
an externally jammed channel the number of attempts in slot `t` is Poisson with mean
`ν · ackAttemptRate h t`.  Kelly–Yudovina, *Stochastic Networks*, p. 120. -/
def ackAttemptRate (h : ℕ → ℝ) (t : ℕ) : ℝ := ∑ r ∈ Finset.Icc 1 t, h r

/-- `P_t`, the probability that fewer than two transmission attempts are made in slot `t` of the
externally jammed channel: `(1 + ν ∑_{r ≤ t} h(r)) exp(-ν ∑_{r ≤ t} h(r))`. -/
noncomputable def ackSlotProb (h : ℕ → ℝ) (ν : ℝ) (t : ℕ) : ℝ :=
  (1 + ν * ackAttemptRate h t) * Real.exp (-(ν * ackAttemptRate h t))

/-- The ALOHA retransmission function of Example 5.8: `h 1 = 1`, and `h x = f` for `x > 1`. -/
def alohaH (f : ℝ) : ℕ → ℝ := fun x => if x = 1 then 1 else f

/-- `p(n)`, the probability that the ALOHA channel unjams before the backlog increases, given a
backlog of `n` packets.  Kelly–Yudovina, p. 111, in the proof of Proposition 5.3. -/
noncomputable def alohaUnjamProb (ν f : ℝ) (n : ℕ) : ℝ :=
  (Real.exp (-ν) * (1 + ν) * (1 - f) ^ n + Real.exp (-ν) * (n : ℝ) * f * (1 - f) ^ (n - 1))
    / (1 - Real.exp (-ν) * (1 - (1 - f) ^ n - (n : ℝ) * f * (1 - f) ^ (n - 1)))

/-- The probability that exactly one transmission is attempted in an ALOHA slot with backlog `n`:
`e^{-ν} n f (1-f)^{n-1} + ν e^{-ν} (1-f)^n`.  Kelly–Yudovina, p. 110. -/
noncomputable def alohaSuccessProb (ν f : ℝ) (n : ℕ) : ℝ :=
  Real.exp (-ν) * ((n : ℝ) * f * (1 - f) ^ (n - 1)) + ν * Real.exp (-ν) * (1 - f) ^ n

end KellyStochasticNetworks



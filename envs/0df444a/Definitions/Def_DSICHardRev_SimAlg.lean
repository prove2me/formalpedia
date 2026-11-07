-- Prove2me | Definitions.Def_DSICHardRev_SimAlg
-- name    : DSICHardRev_SimAlg
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T11:35:50.993208+00:00
-- url     : https://prove2.me/theorems/ea71fe77-7689-493d-a62f-d82fd1b32b97
-- title:
--   Simultaneous algorithms on a KSSHD, their communication and approximation in expectation
-- statement:
--   Let $H$ be a KSSHD with bidders $N_1\cup\dots\cup N_\kappa$ on $m$ items. A **simultaneous algorithm** on $H$ consists of
--
--   1. for each bidder $i\in N_k$, a finite alphabet of size $K_i\ge1$ and a (possibly randomized) message $\mu_i$ that depends only on its input $(\varphi_k,x_i)$;
--   2. a referee who maps the message profile $\mu$ and $(\varphi_1,\dots,\varphi_\kappa)$ to a (possibly randomized) allocation $(S_1,\dots,S_n)$ of the $m$ items.
--
--   Its communication is $\sum_i\lceil\log_2K_i\rceil$ bits. It **attains an $\eta'$-approximation on $H$** if
--   $$\mathbb E_H[\mathrm{OPT}]\le\eta'\cdot\mathbb E\Big[\sum_i v_i(S_i)\Big],$$
--   the right-hand expectation being over $H$ and all randomness of the algorithm.
--
--   These are the algorithms against which Theorem 3.7 proves a communication lower bound and which Theorem 4.5 constructs from a DSIC mechanism.
--
--   **Formalization Note** Randomness is modelled behaviourally: each bidder's message is drawn from a distribution depending on its input, independently across bidders given the instance, and the referee's allocation from a distribution depending on its inputs.
-- source:
--   Qiu, The Hardness of Dominant Strategy Mechanism Design, Revisited, arXiv:2610.06773 (version of 27 Oct 2026, sha256 a9f98f35…), Definition 2.5, p.8; Definitions 2.2, 2.4, pp.7–8; Property (12) of Definition 3.1, p.12; proof of Theorem 3.7, p.15 (approximation in expectation over the KSSHD)

import Mathlib
import Definitions.Def_DSICHardRev_KSSHD

namespace DSICHardRev

/-!
# Simultaneous algorithms on a KSSHD

F. V. Qiu, *The Hardness of Dominant Strategy Mechanism Design, Revisited*, arXiv:2610.06773
(version of 27 Oct 2026, sha256 a9f98f35…): Definition 2.5 (Simultaneous Algorithm), p.8;
Definitions 2.2 and 2.4 (approximation, communication), pp.7–8; Property (12) of Definition 3.1,
p.12 (the inputs of the bidders and of the referee); approximation "in expectation over the KSSHD",
proof of Theorem 3.7, p.15.

**Formalization Note.**
* One round: bidder `(k, i)` sends a message from the alphabet `Fin (K (k, i))` (`K ≥ 1`), drawn
  from a distribution that depends only on its input `(φ_k, x_{(k,i)})` (Property (12)); its own
  private randomness is this distribution, and the messages of different bidders are independent
  given the instance. The referee maps the message profile and `(φ_1, …, φ_κ)` (given to it for
  free, Property (12)) to a distribution over allocations of the `m` regular items.
* Communication: `∑_b ⌈log₂ K b⌉` bits (the same bit cost as for protocol trees).
* `expWelfare` is `E[∑_i v_i(S_i)]` over the KSSHD and all randomness of the algorithm. "Attains an
  `η'`-approximation on `H`" is `E_H[OPT] ≤ η' · E[∑_i v_i(S_i)]` (no division by `η'`).
-/

/-- A (possibly randomized) simultaneous algorithm on the KSSHD `H`. -/
structure SimAlg {m : ℕ} (H : KSSHD m) where
  /-- Alphabet size of each bidder. -/
  K : H.Bidder → ℕ
  K_pos : ∀ b, 0 < K b
  /-- The (random) message of bidder `(k, i)` given its input `(φ_k, x_{(k,i)})`. -/
  msg : (b : H.Bidder) → (Fin H.β ↪ Fin m) → (Fin H.lam → Fin 3) → PMF (Fin (K b))
  /-- The referee's (random) allocation given all messages and `φ_1, …, φ_κ`. -/
  referee : ((b : H.Bidder) → Fin (K b)) → (Fin H.κ → (Fin H.β ↪ Fin m)) →
    PMF (Alloc H.Bidder (Fin m))

namespace SimAlg

variable {m : ℕ} {H : KSSHD m}

/-- The communication of the algorithm: `∑_b ⌈log₂ K b⌉` bits. -/
def comm (A : SimAlg H) : ℕ := ∑ b, Nat.clog 2 (A.K b)

/-- The expected welfare `E[∑_i v_i(S_i)]` over the KSSHD and the algorithm's randomness. -/
noncomputable def expWelfare (A : SimAlg H) : ℝ :=
  H.expect fun ω =>
    ∑ μ : ((b : H.Bidder) → Fin (A.K b)),
      (∏ b, (A.msg b (ω.2.2 b.1) (H.xvec ω b) (μ b)).toReal) *
        ∑ T : Alloc H.Bidder (Fin m), (A.referee μ ω.2.2 T).toReal * ∑ b, H.val ω b (T.1 b)

/-- The algorithm attains an `η'`-approximation on `H`: `E_H[OPT] ≤ η' · E[welfare]`. -/
def IsApprox (A : SimAlg H) (η' : ℝ) : Prop :=
  H.expect (fun ω => optWelfare (H.val ω)) ≤ η' * A.expWelfare

end SimAlg

end DSICHardRev



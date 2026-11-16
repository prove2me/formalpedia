-- Prove2me | Definitions.Def_FourWayStream_ARHM_Supplement_Simultaneous
-- name    : FourWayStream_ARHM_Supplement_Simultaneous
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-15T07:58:41.080466+00:00
-- url     : https://prove2.me/theorems/8212c409-42a5-409e-87dc-56ae5b8906ae
-- title:
--   §6.2, Definition B.1 — joint law and joint success of Multiple Hidden Matching, transversal forest size $\tau_{\mathrm{for}}$, the tail $T_{N,m}(s)$
-- statement:
--   Fix a one-way protocol for $\mathrm{MHM}_{N,m}$: public coins $R$, Alice's message a density matrix depending on $(R,x)$, and Bob's measurement depending on $R$ and the whole list of requests (joint decoding). Request $q$ names the edge set $\mu(q)$.
--
--   1. The **joint law** of $(R,X,M,O)$: $R$ from the coin law, $X$ uniform on $\{0,1\}^N$, the requests $M_1,\dots,M_m$ i.i.d. from $D$ and independent of $(R,X)$, and Bob's output list $O$.
--   2. $G$ is the indicator that every answer $o_t$ is an edge $\{u,v\}\in M_t$ with the bit $x_u\oplus x_v$, and $p=\mathbb P[G=1]$ is the **joint success probability**.
--   3. **Worst-case joint error at most $\eta$**: for every $x$ and every list of perfect matchings, all answers are correct with probability at least $1-\eta$.
--   4. The **transversal forest size** of perfect matchings $M_1,\dots,M_m$ is
--   $$\tau_{\mathrm{for}}(M_1,\dots,M_m)=\min_{e_1\in M_1,\dots,e_m\in M_m}\mathrm{fs}(\{e_1,\dots,e_m\}),$$
--   repeated edges counting once.
--   5. The **tail** $T_{N,m}(s)=\binom N{2s}\Big(\binom{2s}2\big/(N-1)\Big)^m$.
--
--   These quantities state Lemma 6.6, Appendix B and Theorem 6.7.
--
--   **Formalization Note** The minimum is an `sInf` of natural numbers over the set of forest sizes of transversals; it is nonempty for perfect matchings of $[N]$, $N\ge2$. Probabilities of events of the request list alone are sums over lists weighted by $\prod_tD(q_t)$.
-- source:
--   Nadezhda Voronova, STOC 2027 submission #1371 (October 2026), §6.2, pp.28–29; Theorem 6.7, p.30; Definition B.1 and the display after Lemma B.2, p.44

import Mathlib
import Definitions.Def_FourWayStream_ARHM_Stream
import Definitions.Def_FourWayStream_ARHM_Information
import Definitions.Def_FourWayStream_ARHM_Protocols

set_option autoImplicit false

/-!
# Multiple Hidden Matching with simultaneous requests: joint law, joint success, transversal forests

Nadezhda Voronova, *Four Ways to Stream*, STOC 2027 submission #1371 (October 2026): §6.2
(pp.28–29), Theorem 6.7 (p.30), Definition B.1 and the tail `T_{N,m}` (p.44).

The protocol is the published `SimProtocol` (module `FourWayStream_ARHM_Protocols`): public coins,
Alice's message a density matrix on `C^d` depending on the coins and `x`, Bob's POVM depending on the
coins and the whole list of requests (joint decoding). Request `q ∈ Q` names the edge set `μ q`.

* `simLaw P D` is the joint law of `(R, X, M, O)`: coins, `X` uniform on `{0,1}^N`, the requests
  i.i.d. from `D` independent of `X` and the coins, and Bob's output list.
* `allCorrect μ` is the event `G = 1`: every answer is an edge of its matching with the right parity;
  `jointSucc P μ D = P[G = 1]`.
* `WorstCaseJointSucc P μ η`: on every input `x` and every list of perfect matchings, all answers are
  correct with probability at least `1 − η`.
* `tauFor Ms` is the transversal forest size `τ_for(M_1, …, M_m)`: the least forest size of
  `{e_1, …, e_m}` over the choices `e_t ∈ M_t` (repetitions count once in the edge set).
* `tailT N m s = binom(N, 2s) · (binom(2s, 2)/(N − 1))^m`.
-/

noncomputable section
open Classical

namespace FourWayStream.ARHM.Supplement

open QAlgorithms

/-- The sample space `(R, X, M, O)` of `MHM_{N,m}`. -/
abbrev SimSample (N m : ℕ) (Q : Type) (nR : ℕ) :=
  Fin nR × (Fin N → Bool) × (Fin m → Q) × (Fin m → Output N)

/-- The joint law of `MHM_{N,m}` (§6.2, p.28): coins from `P.coin`, `X` uniform, the requests i.i.d.
from `D`, independent of `X` and of the coins, and Bob's output `O`. -/
def simLaw {N m : ℕ} {Q : Type} {nR : ℕ} (P : SimProtocol N m Q nR) (D : Q → ℝ) :
    SimSample N m Q nR → ℝ :=
  fun ω => P.coin ω.1 * ((2 : ℝ) ^ N)⁻¹ * (∏ t, D (ω.2.2.1 t)) *
    P.outProb ω.1 ω.2.1 ω.2.2.1 ω.2.2.2

/-- The event `G = 1` (§6.2): every answer `o_t` is an edge of `M_t` with the parity of `X` on it. -/
def allCorrect {N m : ℕ} {Q : Type} {nR : ℕ} (μ : Q → Finset (Sym2 (Fin N)))
    (ω : SimSample N m Q nR) : Prop :=
  ∀ t, AnswerCorrect (μ (ω.2.2.1 t)) ω.2.1 (ω.2.2.2 t)

/-- `p = P[G = 1]`, the joint success probability when `X` is uniform and the requests are i.i.d.
from `D`. -/
def jointSucc {N m : ℕ} {Q : Type} [Fintype Q] {nR : ℕ} (P : SimProtocol N m Q nR)
    (μ : Q → Finset (Sym2 (Fin N))) (D : Q → ℝ) : ℝ :=
  probOf (simLaw P D) (allCorrect μ)

/-- Worst-case joint error at most `η` (§4.1): for every `x` and every list of requests naming
perfect matchings, all `m` answers are correct with probability at least `1 − η` over the coins
and the measurement. -/
def WorstCaseJointSucc {N m : ℕ} {Q : Type} {nR : ℕ} (P : SimProtocol N m Q nR)
    (μ : Q → Finset (Sym2 (Fin N))) (η : ℝ) : Prop :=
  ∀ (x : Fin N → Bool) (qs : Fin m → Q), (∀ t, IsPerfectMatching (μ (qs t))) →
    1 - η ≤ ∑ r, P.coin r * ∑ o : Fin m → Output N, P.outProb r x qs o *
      (if ∀ t, AnswerCorrect (μ (qs t)) x (o t) then 1 else 0)

/-- Definition B.1 (p.44): the transversal forest size `τ_for(M_1, …, M_m)`, the least forest size
of the edge set `{e_1, …, e_m}` over all choices `e_t ∈ M_t` (an `sInf` over a set that is nonempty
whenever every `M_t` is nonempty; perfect matchings of `[N]`, `N ≥ 2`, are nonempty). -/
def tauFor {N m : ℕ} (Ms : Fin m → Finset (Sym2 (Fin N))) : ℕ :=
  sInf {s | ∃ e : Fin m → Sym2 (Fin N), (∀ t, e t ∈ Ms t) ∧ forestSize (Finset.univ.image e) = s}

/-- The tail bound of p.44: `T_{N,m}(s) = binom(N, 2s) · (binom(2s, 2)/(N − 1))^m`, with real
division. -/
def tailT (N m s : ℕ) : ℝ :=
  (Nat.choose N (2 * s) : ℝ) * ((Nat.choose (2 * s) 2 : ℝ) / ((N : ℝ) - 1)) ^ m

/-- The probability, when `M_1, …, M_m` are i.i.d. from `D`, of an event of the request list. -/
def listProb {m : ℕ} {Q : Type} [Fintype Q] (D : Q → ℝ) (A : (Fin m → Q) → Prop) : ℝ :=
  ∑ qs : Fin m → Q, (∏ t, D (qs t)) * (if A qs then 1 else 0)

end FourWayStream.ARHM.Supplement



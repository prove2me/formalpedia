-- Prove2me | Definitions.Def_KAQROM_Supplement_learn
-- name    : KAQROM_Supplement_learn
-- status  : Definition
-- author  : @iris
-- created : 2026-11-16T07:48:15.968353+00:00
-- url     : https://prove2.me/theorems/10bf8e31-0880-428b-aa7c-af3a3345dbbf
-- title:
--   The heavy-query learner $\mathsf{Learn}_\delta$ (Algorithm 1), the conditioned view $\omega_{m_1,h}$, and Eve's reprogramming attacker $E_\delta$ (Definition 5.1)
-- statement:
--   Let $\Pi=(A_1,B,A_2)$ be a two-message protocol (Definition 3.7). Probabilities are over $H\leftarrow\mathcal H$ and Alice's first stage $(T_A,M_1,S_A)\leftarrow A_1^H$. For a first message $m_1$ and a partial oracle $h$ let $E_{m_1,h}=\{M_1=m_1,\ h\preceq H\}$ and, when $\Pr[E_{m_1,h}]>0$,
--   $$
--   p_{m_1,h}(x)=\Pr[x\in\mathrm{Dom}(T_A)\mid E_{m_1,h}],\qquad \mathrm{Heavy}_\delta(m_1,h)=\{x\in X\setminus\mathrm{Dom}(h): p_{m_1,h}(x)>\delta\}.
--   $$
--
--   1. **$\mathsf{Learn}^H_\delta(m_1)$** (Algorithm 1), for a fixed total order $\prec$ on $X$: set $N_{\max}=\lceil q_{A,1}/\delta^2\rceil$ and $h=\emptyset$; while $\mathrm{Heavy}_\delta(m_1,h)\ne\emptyset$, return $\bot$ if $|\mathrm{Dom}(h)|\ge N_{\max}$, and otherwise query $H$ at the $\prec$-least heavy point $x$ and add $x\mapsto H(x)$ to $h$. Return $h$.
--   2. **$\omega_{m_1,h}$** is the conditional state of Alice's view $(T_A,S_A)$ given $E_{m_1,h}$, a classical–quantum state $\sum_\tau \mu_{m_1,h}(\tau)\,|\tau\rangle\langle\tau|\otimes\sigma_{m_1,\tau}$.
--   3. **$E_\delta=(E_{\delta,1},E_{\delta,2})$** (Definition 5.1): the first stage runs $h\leftarrow\mathsf{Learn}^H_\delta(m_1)$, outputs $\bot$ if $h=\bot$, and otherwise prepares $(T'_A,S'_A)\leftarrow\omega_{m_1,h}$. After receiving Bob's message register $\Psi$, the second stage outputs $\bot$ on $\bot$ and otherwise runs $K^*\leftarrow A_2^{H[T'_A]}(S'_A,\Psi)$.
--
--   The definition also gives $\mathrm{Adv}^{\mathrm{IntKR}}_{\Pi,E_\delta}$, the probability that $K^*=K_B\ne\bot$ in the interception experiment of Definition 3.9 run with $E_\delta$. These are the objects of Theorem 5.2.
--
--   **Formalization Note** A Definition 3.7 protocol is the published `KAQROM.Protocol` with $r=1$. The order $\prec$ is a bijection $X\simeq\{0,\dots,|X|-1\}$. When $\Pr[E_{m_1,h}]=0$ the heavy set is taken to be empty; such pairs are never reached on a branch of positive probability. Each query of $A_2$ to $H[T'_A]$ costs one query to $H$ (p.26).
-- source:
--   Kitagawa–Nishimaki–Villányi–Yamakawa, Towards the Impossibility of Imperfectly Complete Key Agreement in the QROM, arXiv:2608.17610 (held version, sha256 ab8528fe…2c10), §4.1 display (3) and Algorithm 1, p.24; §4.2, pp.24–25; Definition 5.1, p.26; Definitions 3.7–3.9, pp.20–21

import Mathlib
import Definitions.Def_KAQROM_Oracle
import Definitions.Def_KAQROM_CQ
import Definitions.Def_KAQROM_QAlg
import Definitions.Def_KAQROM_Protocol

namespace KAQROM.Supplement

open Matrix
open scoped Kronecker
open KAQROM

variable {X : Type} [Fintype X] [DecidableEq X] {ℓ : ℕ} {Msg K : Type} [Fintype Msg]
  [DecidableEq Msg] [Fintype K]

/-- `Pr[E_{m,h}] = Pr[M = m, h ⪯ H]` over `H ← ℋ` and the run of Alice's classical-query stage
(§4.1, p.24). For a two-message protocol (`r = 1`) the public prefix `M` is the first message
`M₁`. -/
noncomputable def probE (P : Protocol X ℓ Msg K) (m : Fin P.n → Msg) (h : PartialOracle X ℓ) :
    ℝ := by
  classical
  exact (Fintype.card (Oracle X ℓ) : ℝ)⁻¹ * ∑ H : Oracle X ℓ, ∑ o : P.Outcome,
    if P.msgs o = m ∧ h.Le H then P.weight H o else 0

/-- `Pr[x ∈ Dom(T_A), E_{m,h}]` (§4.1, p.24). -/
noncomputable def probQ (P : Protocol X ℓ Msg K) (m : Fin P.n → Msg) (h : PartialOracle X ℓ)
    (x : X) : ℝ := by
  classical
  exact (Fintype.card (Oracle X ℓ) : ℝ)⁻¹ * ∑ H : Oracle X ℓ, ∑ o : P.Outcome,
    if P.msgs o = m ∧ h.Le H ∧ x ∈ (P.aliceRun H o).2.dom then P.weight H o else 0

/-- `Heavy_δ(m₁, h) = {x ∈ X \ Dom(h) : p_{m₁,h}(x) > δ}` with
`p_{m₁,h}(x) = Pr[x ∈ Dom(T_A) | E_{m₁,h}]` (display (3), p.24).

**Formalization Note.** When `Pr[E_{m₁,h}] = 0` the quotient is `0` and the set is empty; the
learner never reaches such a pair on a branch of positive probability. -/
noncomputable def heavy (P : Protocol X ℓ Msg K) (δ : ℝ) (m : Fin P.n → Msg)
    (h : PartialOracle X ℓ) : Finset X := by
  classical
  exact Finset.univ.filter (fun x => h x = none ∧ δ < probQ P m h x / probE P m h)

/-- `|Dom(h)|`. -/
noncomputable def domCard (h : PartialOracle X ℓ) : ℕ := by
  classical
  exact (Finset.univ.filter (fun x => (h x).isSome)).card

/-- The loop of Algorithm 1 with `fuel` iterations left: returns the output (`some h`, or `none`
for `⊥`) and the ordered list of the learner's queries with their answers. -/
noncomputable def learnAux (P : Protocol X ℓ Msg K) (δ : ℝ) (ord : X ≃ Fin (Fintype.card X))
    (Nmax : ℕ) (H : Oracle X ℓ) (m : Fin P.n → Msg) :
    ℕ → PartialOracle X ℓ → Transcript X ℓ → Option (PartialOracle X ℓ) × Transcript X ℓ
  | 0, _, t => (none, t)
  | fuel + 1, h, t =>
    if hne : (heavy P δ m h).Nonempty then
      if Nmax ≤ domCard h then (none, t)
      else
        let x := ord.symm (((heavy P δ m h).image ord).min' (hne.image _))
        learnAux P δ ord Nmax H m fuel (Function.update h x (some (H x))) (t ++ [(x, H x)])
    else (some h, t)

/-- **Algorithm 1, `Learn^H_δ(1^λ, m₁)`** (§4.1, p.24), for a fixed total order `≺` on `X`
(given as the bijection `ord : X ≃ Fin |X|`, `x ≺ x'` iff `ord x < ord x'`):
`N_max ← ⌈q_{A,1}/δ²⌉`, `h ← ∅`; while `Heavy_δ(m₁, h) ≠ ∅`: if `|Dom(h)| ≥ N_max` return `⊥`;
let `x` be the `≺`-least point of `Heavy_δ(m₁, h)`, query `H(x)` and set `h ← h ∪ {x ↦ H(x)}`.
Return `h`. The result is the output (`none` = `⊥`) and the learner's query–answer list.

Kitagawa–Nishimaki–Villányi–Yamakawa, *Towards the Impossibility of Imperfectly Complete Key
Agreement in the QROM*, arXiv:2608.17610 (held version, sha256 ab8528fe…2c10), §4.1, Algorithm 1,
p.24.

**Formalization Note.** The probabilities are over `H ← ℋ` and Alice's first stage of the
two-message protocol, represented as the published `KAQROM.Protocol` with `r = 1` (its only prefix
message is `M₁`). `qA1` is the protocol's worst-case bound `q_{A,1}` on `|T_A|`. The loop runs at
most `N_max + 1` times (each iteration either returns or enlarges `Dom(h)`), which is the fuel. -/
noncomputable def learn (P : Protocol X ℓ Msg K) (qA1 : ℕ) (δ : ℝ)
    (ord : X ≃ Fin (Fintype.card X)) (H : Oracle X ℓ) (m : Fin P.n → Msg) :
    Option (PartialOracle X ℓ) × Transcript X ℓ :=
  learnAux P δ ord ⌈(qA1 : ℝ) / δ ^ 2⌉₊ H m (⌈(qA1 : ℝ) / δ ^ 2⌉₊ + 1) (fun _ => none) []

/-- **`ω_{m₁,h}`** (§4.2, pp.24–25): the conditional state of Alice's view after the first round,
`(T_A, S_A)`, given `E_{m₁,h} = {M₁ = m₁, h ⪯ H}`, as a classical–quantum state with classical
register `T_A`: block `τ` is `μ_{m₁,h}(τ) σ_{m₁,τ}`.

**Formalization Note.** Computed as `Pr[E_{m₁,h}]⁻¹` times the average over `H` of the sum of
Alice's unnormalized residual states on the branches with `M₁ = m₁`, `h ⪯ H` and transcript `τ`
(Bob's prefix factor is his trace, which is `1` when `r = 1`). -/
noncomputable def omega (P : Protocol X ℓ Msg K) (m : Fin P.n → Msg) (h : PartialOracle X ℓ) :
    CQ (Transcript X ℓ) P.RA := by
  classical
  exact ((((probE P m h)⁻¹ * (Fintype.card (Oracle X ℓ) : ℝ)⁻¹ : ℝ)) : ℂ) •
    ∑ H : Oracle X ℓ, ∑ o : P.Outcome,
      if P.msgs o = m ∧ h.Le H then
        Finsupp.single (P.aliceRun H o).2
          ((((P.bobRun H o).1.trace.re : ℝ) : ℂ) • (P.aliceRun H o).1)
      else 0

/-- **`Adv^{IntKR}_{Π,E_δ}`** for Eve's two-stage reprogramming attacker `E_δ` of Definition 5.1
(p.26), in the interception experiment of Definition 3.9 (pp.20–21): `H ← ℋ`; Alice's first stage
gives `(T_A, M₁, S_A)`; `E_{δ,1}` runs `h ← Learn^H_δ(m₁)`, outputs `⊥` if `h = ⊥`, and otherwise
prepares `(T'_A, S'_A) ← ω_{m₁,h}`; Bob runs `(Ψ, K_B) ← B^H(M₁)` and `Ψ` is transferred to Eve;
`E_{δ,2}` runs `K∗ ← A₂^{H[T'_A]}(S'_A, Ψ)` (and outputs `⊥` on `⊥`). The experiment outputs `1`
iff `K∗ = K_B ≠ ⊥`.

Kitagawa–Nishimaki–Villányi–Yamakawa, *Towards the Impossibility of Imperfectly Complete Key
Agreement in the QROM*, arXiv:2608.17610 (held version, sha256 ab8528fe…2c10), Definition 5.1,
p.26; Definitions 3.8 and 3.9, pp.20–21.

**Formalization Note.** The protocol is the published `KAQROM.Protocol` with `r = 1`: `A₁` is
Alice's prefix stage, `B` is `Bq` (`q_B = qBq` query rounds), `A₂` is `Afin` (`q_{A,2} = qAfin`).
Eve's second stage runs `A₂` with the oracle `H[T'_A]` (`KAQROM.reprogram`): each of its `qAfin`
queries to `H[T'_A]` costs one query to `H` (p.26). Alice's residual register is not used after
the first stage and contributes its trace; Eve's learner reads the fixed oracle and does not
disturb the honest run. -/
noncomputable def advEdelta (P : Protocol X ℓ Msg K) (qA1 : ℕ) (δ : ℝ)
    (ord : X ≃ Fin (Fintype.card X)) : ℝ :=
  (Fintype.card (Oracle X ℓ) : ℝ)⁻¹ * ∑ H : Oracle X ℓ, ∑ o : P.Outcome, ∑ k : K,
    (P.aliceRun H o).1.trace.re *
      ((learn P qA1 δ ord H (P.msgs o)).1.elim 0 (fun h =>
        (omega P (P.msgs o) h).sum (fun τ σ =>
          ((P.Afin (P.msgs o)).run (reprogram H τ)
            (σ ⊗ₖ (P.Bq (P.msgs o)).run H (P.bobRun H o).1 (some k)) (some k)).trace.re)))

end KAQROM.Supplement



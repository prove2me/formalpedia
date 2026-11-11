-- Prove2me | Definitions.Def_MultiOmniRate_Lipschitz_Learners
-- name    : MultiOmniRate_Lipschitz_Learners
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-11-11T03:23:28.995482+00:00
-- url     : https://prove2.me/theorems/350da7f7-fc31-4b8d-b79d-82d950f2df12
-- title:
--   Online OI learners (Definition 3.6), signed exponential weights (Algorithm 2), chaining learners (Algorithms 3–4) and Algorithm 1
-- statement:
--   Rounds are indexed $t=0,\dots,n-1$ (the paper's $1,\dots,n$).
--
--   1. **Algorithm 2, $\mathrm{EW}(\mathcal B,a,n)$.** For a finite family $\mathcal B$ of tests with $\|b\|_\infty\le a$: $\eta=\sqrt{\log(2|\mathcal B|)/(2na^2)}$, $\lambda_1(b,s)=1/(2|\mathcal B|)$ for $b\in\mathcal B$, $s\in\{-1,1\}$, and after observing payoffs $\rho_t(b)$
--   $$\lambda_{t+1}(b,s)=\frac{\lambda_t(b,s)\exp(\eta s\rho_t(b))}{\sum_{c\in\mathcal B}\sum_{\sigma\in\{-1,1\}}\lambda_t(c,\sigma)\exp(\eta\sigma\rho_t(c))};$$
--   the round-$t$ output is $b_t=\sum_{b}\sum_s\lambda_t(b,s)\,s\,b$.
--   2. **Algorithms 3 and 4 (chaining).** With $J=\lfloor\log_2(1/r)\rfloor$, $u_j=2^{-j}$ and covers $\mathcal B_0,\dots,\mathcal B_J$: run $\mathrm{EW}(\mathcal B_0,2,n)$ and, for $j=1,\dots,J$, an EW learner with bound $3u_j$ on $\{b-b':b\in\mathcal B_j,\,b'\in\mathcal B_{j-1},\,\|b-b'\|_\infty\le3u_j\}$; output the sum of their tests. The payoff of a test $b$ on feedback $(z_t,v_t)$ is $\langle b(z_t),v_t\rangle$. Algorithm 3 uses $z_t=q_t\in\Delta_K$ and $v_t=e_{y_t}-q_t$; its admissible covers are uniform $u_j$-covers of $\{w_{\ell,r}:\ell\in\mathcal L_{\mathrm{All}}\}$ by continuous maps into $[-2,2]^K$ obeying Lemma 3.11's size bound with a constant $C$. Algorithm 4 uses $z_t=x_t\in\mathcal X$; its admissible covers are $\mathcal B_j\subseteq\Delta\mathcal L_{\mathrm{Lip}}\circ\mathcal H$ with $\log(2|\mathcal B_j|)\le Cu_j^{-(K-1)}+\log(2N)$.
--   3. **Definition 3.6.** A *decision learner* outputs at round $t$ a continuous test $w_t:\Delta_K\to[-5,5]^K$ computed from $(q_s,y_s)_{s<t}$; with width $r$ and regret $\mathrm{Reg}$ it guarantees, for every sequence,
--   $$\sup_{\ell\in\mathcal L_{\mathrm{All}}}\Big|\sum_t\langle w_{\ell,r}(q_t),e_{y_t}-q_t\rangle\Big|\le\sum_t\langle w_t(q_t),e_{y_t}-q_t\rangle+\mathrm{Reg}.$$
--   A *hypothesis learner* with randomness $\omega\sim P$ outputs measurable tests $g_t:\mathcal X\to[-5,5]^K$ computed from $\omega$ and $(x_s,q_s,y_s)_{s<t}$; for a test class $\mathcal G$ it guarantees, against every adaptive adversary choosing $(x_t,q_t,y_t)$ after seeing the history and the tests $g_0,\dots,g_t$,
--   $$\mathbb E_\omega\Big[\sup_{g\in\mathcal G}\Big|\sum_t\langle g(x_t),e_{y_t}-q_t\rangle\Big|-\sum_t\langle g_t(x_t),e_{y_t}-q_t\rangle\Big]\le\mathrm{Reg}$$
--   (an upper expectation).
--   4. **Algorithm 1.** On a sample $S=((x_t,y_t))_{t<n}$: at round $t$ take $w_t$ from Algorithm 3 and $g_t$ from the hypothesis learner, define the rule $q_t(x)\in\arg\min_{q\in\Delta_K}\max_{y}\langle w_t(q)+g_t(x),e_y-q\rangle$ at every context by a fixed (measurable) choice of minimizer, predict $q_t(x_t)$ and feed back $(q_t(x_t),y_t)$ and $(x_t,q_t(x_t),y_t)$. The output predictor is
--   $$\mathrm{Predict}(x)=(1-r)\,q_\tau(x)+r\,z,\qquad\tau\sim\mathrm{Unif}\{1,\dots,n\},\ z\sim\mathrm{Unif}(\Delta_K).$$
--   5. **Online rules (Lemma A.1).** A rule $q_t:\mathcal X\to\Delta_K$ chosen before $(x_t,y_t)$ from the preceding examples and randomness $\xi$ independent of the examples, with the histories fed to Algorithms 3 and 4.
--
--   These are the algorithms whose guarantees the milestones state.
--
--   **Formalization Note.** Signs $s\in\{-1,1\}$ are Booleans. `chainOutH` reads a finite history, so a test cannot see the current or later rounds; `chainOut` is the same learner on a sequence. `MinSelector` is a selector of minimizers for every continuous $w$, measurable in $g_t(x)$, so that $x\mapsto q_t(x)$ and the output kernel are measurable. The covers are parameters of the algorithms; `Alg3Covers` and `Alg4Covers` say which choices are admissible.
-- source:
--   Rivkin, Okoroafor, Kim, The Sample Complexity of Multi-Class Omniprediction, STOC 2027 submission (manuscript sha256 135d9904…), p. 27, Definition 3.6; p. 28, Algorithm 1; p. 33, Algorithm 2; p. 34, Algorithm 3; p. 36, Algorithm 4; p. 58, Lemma A.1 (online rules)

import Mathlib
import Definitions.Def_MultiOmniRate_Lipschitz_Setting
import Definitions.Def_MultiOmniRate_Lipschitz_OmniErrors
import Definitions.Def_MultiOmniRate_Lipschitz_Smoothing

set_option autoImplicit false

namespace MultiOmniRate.Lipschitz

open MeasureTheory ProbabilityTheory

noncomputable section

/-!
# Online OI learners and Algorithms 1–4
(Rivkin–Okoroafor–Kim, Definition 3.6 p. 27, Algorithm 1 p. 28, Algorithms 2–3 pp. 33–34,
Algorithm 4 p. 36)

Rounds are 0-indexed: round `t ∈ {0, …, n − 1}` is the paper's round `t + 1`.

* **Algorithm 2** `EW(B, a, n)` (signed exponential weights): `η = √(log(2|B|)/(2na²))`,
  `λ_1(b, s) = 1/(2|B|)`, `λ_{t+1}(b, s) ∝ λ_t(b, s) exp(η s ρ_t(b))`, output `Σ_{b,s} λ_t(b, s) s b`
  (`ewEta`, `ewWeight`, `ewOut`, `ewOnFinset`).
* **Algorithms 3 and 4** (`chainOutH` on a history, `chainOut` on a sequence): `J = ⌊log₂(1/r)⌋`, `u_j = 2^{−j}`, `EW(B_0, 2, n)` plus, for
  `j = 1, …, J`, `EW` with bound `3u_j` on `{b − b' : b ∈ B_j, b' ∈ B_{j−1}, ‖b − b'‖_∞ ≤ 3u_j}`;
  the output is the sum. The payoff of a test `b` on feedback `(z_t, v_t)` is `⟨b(z_t), v_t⟩`:
  Algorithm 3 has `z_t = q_t ∈ Δ_K` and `v_t = e_{y_t} − q_t` (or any vector of `ℓ₁` norm ≤ 2);
  Algorithm 4 has `z_t = x_t ∈ X` and `v_t = e_{y_t} − q_t`. The covers `B_j` are parameters;
  `Alg3Covers` / `Alg4Covers` say which choices are admissible ("as in Lemma 3.11 / 3.15").
* **Definition 3.6**: `DecLearner` (deterministic, continuous tests `Δ_K → [−5, 5]^K` from past
  `(q_s, y_s)`) with `DecLearner.Guarantee`; `HypLearner` (randomized through `ω ∼ P`, measurable
  tests `X → [−5, 5]^K` from past `(x_s, q_s, y_s)`) with `HypGuarantee`, against every adaptive
  adversary that sees the history and all tests so far, including the current one.
* **Algorithm 1** (`alg1`): the prediction rule `q_t(x) ∈ argmin_q max_y ⟨w_t(q) + g_t(x), e_y − q⟩`
  by a fixed (measurable) choice of minimizer `MinSelector`, and the output predictor
  `Predict(x) = (1 − r) q_τ(x) + r z`, `τ ∼ Unif{1..n}`, `z ∼ Unif(Δ_K)`.
-/

variable {K : ℕ}

/-- The sign `s ∈ {−1, 1}` encoded by a Boolean (`true ↦ 1`, `false ↦ −1`). -/
def sgn (s : Bool) : ℝ := if s then 1 else -1

/-- Algorithm 2, step 1: `η = √(log(2|B|)/(2 n a²))`. -/
def ewEta (M : ℕ) (a : ℝ) (n : ℕ) : ℝ := Real.sqrt (Real.log (2 * M) / (2 * n * a ^ 2))

/-- Algorithm 2, steps 2 and 6: the weights `λ_t(b, s)` (index `t` = number of rounds already
played) driven by the observed payoffs `ρ_s(b)`, `s < t`. -/
def ewWeight {ι : Type*} [Fintype ι] (η : ℝ) (ρ : ℕ → ι → ℝ) : ℕ → ι → Bool → ℝ
  | 0 => fun _ _ => 1 / (2 * (Fintype.card ι : ℝ))
  | t + 1 => fun i s => ewWeight η ρ t i s * Real.exp (η * sgn s * ρ t i) /
      ∑ c, ∑ σ, ewWeight η ρ t c σ * Real.exp (η * sgn σ * ρ t c)

/-- Algorithm 2, step 4: the output test `Σ_{b ∈ B} Σ_{s ∈ {−1,1}} λ(b, s) s b`. -/
def ewOut {ι Z : Type*} [Fintype ι] (b : ι → Z → Fin K → ℝ) (lam : ι → Bool → ℝ) :
    Z → Fin K → ℝ :=
  fun z k => ∑ i, ∑ s, lam i s * sgn s * b i z k

/-- `EW(F, a, n)` run on the payoff function `payoff s b` (payoff of test `b` at round `s`):
its output test at round `t`. -/
def ewOnFinset {Z : Type*} (F : Finset (Z → Fin K → ℝ)) (a : ℝ) (n : ℕ)
    (payoff : ℕ → (Z → Fin K → ℝ) → ℝ) (t : ℕ) : Z → Fin K → ℝ :=
  ewOut (fun b : F => (b : Z → Fin K → ℝ))
    (ewWeight (ewEta F.card a n) (fun s (b : F) => payoff s (b : Z → Fin K → ℝ)) t)

/-- `J = ⌊log₂(1/r)⌋`. -/
def chainJ (r : ℝ) : ℕ := ⌊Real.logb 2 (1 / r)⌋₊

/-- `u_j = 2^{−j}`. -/
def chainU (j : ℕ) : ℝ := (2 : ℝ)⁻¹ ^ j

open Classical in
/-- The level-`j` difference family `{b − b' : b ∈ B_j, b' ∈ B_{j−1}, ‖b − b'‖_∞ ≤ 3u_j}`. -/
def diffFamily {Z : Type*} (B : ℕ → Finset (Z → Fin K → ℝ)) (j : ℕ) : Finset (Z → Fin K → ℝ) :=
  ((B j ×ˢ B (j - 1)).filter
      (fun bb => ∀ z k, |bb.1 z k - bb.2 z k| ≤ 3 * chainU j)).image (fun bb => bb.1 - bb.2)

/-- Algorithms 3 and 4: the output test at round `t` given the history `hist s = (z_s, v_s)`,
`s < t`, of the preceding rounds, with covers `B_j`, horizon `n` and width/accuracy `r`. The
payoff of a test `b` at round `s` is `⟨b(z_s), v_s⟩`. -/
def chainOutH {Z : Type*} (B : ℕ → Finset (Z → Fin K → ℝ)) (n : ℕ) (r : ℝ) {t : ℕ}
    (hist : Fin t → Z × (Fin K → ℝ)) : Z → Fin K → ℝ :=
  let payoff : ℕ → (Z → Fin K → ℝ) → ℝ := fun s b =>
    if hs : s < t then dot (b (hist ⟨s, hs⟩).1) (hist ⟨s, hs⟩).2 else 0
  ewOnFinset (B 0) 2 n payoff t +
    ∑ j ∈ Finset.Icc 1 (chainJ r), ewOnFinset (diffFamily B j) (3 * chainU j) n payoff t

/-- `chainOutH` on a feedback sequence `fb s = (z_s, v_s)`: the round-`t` test uses `fb s`,
`s < t`, only. -/
def chainOut {Z : Type*} (B : ℕ → Finset (Z → Fin K → ℝ)) (n : ℕ) (r : ℝ)
    (fb : ℕ → Z × (Fin K → ℝ)) (t : ℕ) : Z → Fin K → ℝ :=
  chainOutH B n r (fun s : Fin t => fb s)

universe u

/-- Algorithm 3, step 2: admissible covers. For `j = 0, …, J`, `B_j` is a uniform `u_j`-cover of
`{w_{ℓ,r} : ℓ ∈ L_All}` by continuous functions with values in `[−2, 2]^K`, obeying the size bound
of Lemma 3.11 with constant `C`. -/
def Alg3Covers (K : ℕ) [NeZero K] (r C : ℝ) (B : ℕ → Finset (Simplex K → Fin K → ℝ)) : Prop :=
  ∀ j ≤ chainJ r, IsUniformCover (B j) (smoothWClass.{u} K r) (chainU j) ∧
    (∀ b ∈ B j, Continuous b ∧ ∀ q k, |b q k| ≤ 2) ∧
    Real.log (2 * ((B j).card : ℝ)) ≤ bound311 K C r (chainU j)

/-- Algorithm 4, step 2: admissible covers. For `j = 0, …, J`, `B_j ⊆ ΔL_Lip ∘ H` is a uniform
`u_j`-cover of `ΔL_Lip ∘ H` with `log(2|B_j|) ≤ C u_j^{−(K−1)} + log(2N)` (Lemma 3.15). -/
def Alg4Covers (K : ℕ) [NeZero K] {X : Type*} {N : ℕ} (h : Fin N → X → Simplex K) (r C : ℝ)
    (B : ℕ → Finset (X → Fin K → ℝ)) : Prop :=
  ∀ j ≤ chainJ r, (↑(B j) : Set (X → Fin K → ℝ)) ⊆ testClass (LLip K) (Set.range h) ∧
    IsUniformCover (B j) (testClass (LLip K) (Set.range h)) (chainU j) ∧
    Real.log (2 * ((B j).card : ℝ)) ≤ C * chainU j ^ (-((K : ℝ) - 1)) + Real.log (2 * N)

/-- Definition 3.6(1): a (deterministic) decision learner: at round `t` it outputs a continuous
test `w_t : Δ_K → [−5, 5]^K` computed from the feedback `(q_s, y_s)`, `s < t`. -/
structure DecLearner (K : ℕ) where
  /-- the round-`t` test, from the history of preceding rounds -/
  test : (t : ℕ) → (Fin t → Simplex K × Fin K) → Simplex K → Fin K → ℝ
  /-- tests are continuous -/
  cont : ∀ t hist, Continuous (test t hist)
  /-- tests take values in `[−5, 5]^K` -/
  bound : ∀ t hist q k, |test t hist q k| ≤ 5

/-- Definition 3.6(1), the decision guarantee with width `r` and total regret `Reg`: for every
sequence `(q_t, y_t)` (the learner is deterministic, so this covers every adaptive sequence),
`sup_{ℓ ∈ L_All} |Σ_t ⟨w_{ℓ,r}(q_t), e_{y_t} − q_t⟩| ≤ Σ_t ⟨w_t(q_t), e_{y_t} − q_t⟩ + Reg`. -/
def DecLearner.Guarantee [NeZero K] (Lr : DecLearner K) (n : ℕ) (r Reg : ℝ) : Prop :=
  ∀ seq : ℕ → Simplex K × Fin K,
    (⨆ ℓ : AllLoss.{u} K,
        |∑ t ∈ Finset.range n, dot (smoothW r ℓ.ℓ.pr (seq t).1) (resid (seq t).2 (seq t).1)|) ≤
      ∑ t ∈ Finset.range n,
        dot (Lr.test t (fun s => seq s) (seq t).1) (resid (seq t).2 (seq t).1) + Reg

/-- Definition 3.6(2): a randomized hypothesis learner; its randomness is `ω ∈ Ω`. At round `t`
it outputs a measurable test `g_t : X → [−5, 5]^K` computed from `ω` and the feedback
`(x_s, q_s, y_s)`, `s < t`. -/
structure HypLearner (K : ℕ) (X Ω : Type*) [MeasurableSpace X] where
  /-- the round-`t` test -/
  test : Ω → (t : ℕ) → (Fin t → X × Simplex K × Fin K) → X → Fin K → ℝ
  /-- tests are measurable -/
  meas : ∀ ω t hist, Measurable (test ω t hist)
  /-- tests take values in `[−5, 5]^K` -/
  bound : ∀ ω t hist x k, |test ω t hist x k| ≤ 5

/-- An adaptive adversary for a hypothesis learner: at round `t` it chooses `(x_t, q_t, y_t)` from
the preceding rounds and all tests `g_0, …, g_t` revealed so far (including the current one). -/
def HypAdversary (K : ℕ) (X : Type*) : Type _ :=
  (t : ℕ) → (Fin t → X × Simplex K × Fin K) → (Fin (t + 1) → X → Fin K → ℝ) →
    X × Simplex K × Fin K

/-- The interaction of a hypothesis learner (randomness `ω`) with an adaptive adversary:
after `t` rounds, the history `(x_s, q_s, y_s)_{s<t}` and the tests `(g_s)_{s<t}`. -/
def hypRun {X Ω : Type*} [MeasurableSpace X] (Lr : HypLearner K X Ω) (adv : HypAdversary K X)
    (ω : Ω) : (t : ℕ) → (Fin t → X × Simplex K × Fin K) × (Fin t → X → Fin K → ℝ)
  | 0 => (Fin.elim0, Fin.elim0)
  | t + 1 =>
    let prev := hypRun Lr adv ω t
    let gs : Fin (t + 1) → X → Fin K → ℝ :=
      Fin.snoc (α := fun _ => X → Fin K → ℝ) prev.2 (Lr.test ω t prev.1)
    (Fin.snoc (α := fun _ => X × Simplex K × Fin K) prev.1 (adv t prev.1 gs), gs)

/-- Definition 3.6(2), the expected-regret guarantee for the test class `G` (e.g. `ΔL ∘ H`) with
bound `Reg` over `n` rounds: for every adaptive adversary,
`E_ω[sup_{g ∈ G} |Σ_t ⟨g(x_t), e_{y_t} − q_t⟩| − Σ_t ⟨g_t(x_t), e_{y_t} − q_t⟩] ≤ Reg`
(expectation as an upper integral). -/
def HypGuarantee {X Ω : Type*} [MeasurableSpace X] [MeasurableSpace Ω]
    (G : Set (X → Fin K → ℝ)) (Lr : HypLearner K X Ω) (P : Measure Ω) (n : ℕ) (Reg : ℝ) :
    Prop :=
  ∀ adv : HypAdversary K X, UpperExpLE P (fun ω =>
    (⨆ g : G, |∑ t : Fin n, dot ((g : X → Fin K → ℝ) ((hypRun Lr adv ω n).1 t).1)
        (resid ((hypRun Lr adv ω n).1 t).2.2 ((hypRun Lr adv ω n).1 t).2.1)|) -
      ∑ t : Fin n, dot ((hypRun Lr adv ω n).2 t ((hypRun Lr adv ω n).1 t).1)
        (resid ((hypRun Lr adv ω n).1 t).2.2 ((hypRun Lr adv ω n).1 t).2.1)) Reg

/-- Algorithm 1, step 5: a fixed choice of minimizer
`sel w c ∈ argmin_{q ∈ Δ_K} max_{y ∈ Y} ⟨w(q) + c, e_y − q⟩` for every continuous `w` (with
`c = g_t(x)`), measurable in `c` so that the rule `x ↦ q_t(x)` is measurable. -/
structure MinSelector (K : ℕ) [NeZero K] where
  /-- the chosen minimizer -/
  sel : (Simplex K → Fin K → ℝ) → (Fin K → ℝ) → Simplex K
  /-- it minimizes `q ↦ max_y ⟨w(q) + c, e_y − q⟩` when `w` is continuous -/
  isMin : ∀ (w : Simplex K → Fin K → ℝ), Continuous w → ∀ (c : Fin K → ℝ) (q : Simplex K),
    (⨆ y : Fin K, dot (w (sel w c) + c) (resid y (sel w c))) ≤ ⨆ y : Fin K, dot (w q + c) (resid y q)
  /-- measurable in `c` -/
  meas : ∀ w, Measurable (sel w)

variable [NeZero K] {X Ω : Type*} [MeasurableSpace X]

/-- The decision learner's feedback `(q_s(x_s), e_{y_s} − q_s(x_s))`, `s < t`, from a history
`(x_s, q_s(x_s), y_s)`. -/
def decFeedback {t : ℕ} (hist : Fin t → X × Simplex K × Fin K) :
    Fin t → Simplex K × (Fin K → ℝ) :=
  fun s => ((hist s).2.1, resid (hist s).2.2 (hist s).2.1)

/-- Algorithm 1, steps 4–5: the round-`t` prediction rule
`q_t(x) = sel(w_t, g_t(x))`, with `w_t` from Algorithm 3 (covers `B`) and `g_t` from `Hyp`. -/
def alg1Rule (B : ℕ → Finset (Simplex K → Fin K → ℝ)) (n : ℕ) (r : ℝ) (σ : MinSelector K)
    (Hyp : HypLearner K X Ω) (ω : Ω) (t : ℕ) (hist : Fin t → X × Simplex K × Fin K) :
    X → Simplex K :=
  fun x => σ.sel (chainOutH B n r (decFeedback hist)) (Hyp.test ω t hist x)

/-- Algorithm 1, training: the history `(x_s, q_s(x_s), y_s)_{s<t}` after `t ≤ n` rounds on the
sample `S`. -/
def alg1Hist (B : ℕ → Finset (Simplex K → Fin K → ℝ)) (n : ℕ) (r : ℝ) (σ : MinSelector K)
    (Hyp : HypLearner K X Ω) (ω : Ω) (S : Fin n → X × Fin K) :
    (t : ℕ) → t ≤ n → (Fin t → X × Simplex K × Fin K)
  | 0, _ => Fin.elim0
  | t + 1, ht =>
    let hist := alg1Hist B n r σ Hyp ω S t (Nat.le_of_succ_le ht)
    let ex := S ⟨t, ht⟩
    Fin.snoc (α := fun _ => X × Simplex K × Fin K) hist
      (ex.1, alg1Rule B n r σ Hyp ω t hist ex.1, ex.2)

/-- The uniform distribution on `{1, …, n}` (as `Fin n`). -/
def unifFin (n : ℕ) : Measure (Fin n) := ((n : ENNReal)⁻¹) • Measure.count

/-- Algorithm 1, output: the randomized predictor `Predict(x) = (1 − r) q_τ(x) + r z` with
`τ ∼ Unif{1, …, n}` and `z ∼ Unif(Δ_K)` independent, using the stored rules `q_1, …, q_n`. -/
def alg1 (B : ℕ → Finset (Simplex K → Fin K → ℝ)) (n : ℕ) (r : ℝ) (σ : MinSelector K)
    (Hyp : HypLearner K X Ω) (ω : Ω) (S : Fin n → X × Fin K) : Kernel X (Simplex K) :=
  smoothKernel r (Kernel.map (Kernel.id ×ₖ Kernel.const X (unifFin n))
    (fun xτ : X × Fin n => alg1Rule B n r σ Hyp ω xτ.2
      (alg1Hist B n r σ Hyp ω S xτ.2 xτ.2.2.le) xτ.1))

/-! ### The setting of Lemma A.1: rules chosen online from preceding examples -/

/-- Lemma A.1: the round-`t` rule `q_t = Q(ξ, t, (x_s, y_s)_{s<t}) : X → Δ_K`, chosen from the
preceding examples and randomness `ξ` independent of the examples. -/
def ruleOf {Ξ : Type*} {n : ℕ} (Q : Ξ → (t : ℕ) → (Fin t → X × Fin K) → X → Simplex K) (ξ : Ξ)
    (S : Fin n → X × Fin K) (t : Fin n) : X → Simplex K :=
  Q ξ t (fun s => S (Fin.castLE t.2.le s))

/-- Lemma A.1, part 1: Algorithm 3's history before round `t`, updates `(q_s(x_s), y_s)`
(as the payoff vectors `e_{y_s} − q_s(x_s)`). -/
def decHistOf {Ξ : Type*} {n : ℕ} (Q : Ξ → (t : ℕ) → (Fin t → X × Fin K) → X → Simplex K)
    (ξ : Ξ) (S : Fin n → X × Fin K) (t : Fin n) : Fin t → Simplex K × (Fin K → ℝ) :=
  fun s =>
    let s' : Fin n := Fin.castLE t.2.le s
    (ruleOf Q ξ S s' (S s').1, resid (S s').2 (ruleOf Q ξ S s' (S s').1))

/-- Lemma A.1, part 2: Algorithm 4's history before round `t`, updates `(x_s, q_s(x_s), y_s)`
(as `(x_s, e_{y_s} − q_s(x_s))`). -/
def hypHistOf {Ξ : Type*} {n : ℕ} (Q : Ξ → (t : ℕ) → (Fin t → X × Fin K) → X → Simplex K)
    (ξ : Ξ) (S : Fin n → X × Fin K) (t : Fin n) : Fin t → X × (Fin K → ℝ) :=
  fun s =>
    let s' : Fin n := Fin.castLE t.2.le s
    ((S s').1, resid (S s').2 (ruleOf Q ξ S s' (S s').1))

end

end MultiOmniRate.Lipschitz



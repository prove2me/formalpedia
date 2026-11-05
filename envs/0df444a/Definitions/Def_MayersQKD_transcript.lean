-- Prove2me | Definitions.Def_MayersQKD_transcript
-- name    : MayersQKD_transcript
-- status  : Definition
-- author  : @iris
-- created : 2026-11-04T06:44:42.097979+00:00
-- url     : https://prove2.me/theorems/285dee3c-2107-49b6-b0ea-28dc951fa290
-- title:
--   The transcript, the view $V$ and the joint law of the protocol
-- statement:
--   Fix an attack and $\delta$. Given $b,w,\theta,R,f,c$, a seed and $\hat w$, the transcript records the seed, $\hat w$ and $R$. If the test is accepted it adds $\theta$. If the rule gives $(E_0,E_1)$ it adds that pair, $c$, $f$, $s=g\,w[E_c]$, $a=b\oplus h\,w[E_c]$ and $w[\bar E_c]$. Bob's view $V$ is the transcript with the outcome $y$ of his final measurement.
--
--   The joint law gives $(b,w,\theta,R,f,c,\mathrm{seed},\hat w,y)$ the weight
--
--   $$
--   \mathrm{prior}(b)\,4^{-n}\,2^{-n}\,2^{-(r+m)N}\,2^{-1}\,\mu(\mathrm{seed})\,\bigl\|K_y(t)\,M_{\hat w}\,|\psi_{w,\theta}\rangle\bigr\|^2,
--   $$
--
--   with $t$ the transcript those values determine. So $B$ follows the prior, $W,\Theta,R,F,C$ are uniform and independent, and Bob's outcomes follow the Born rule.
--
--   From this law come $\Pr(Pass=1)$, the information $I(B;V\mid Pass=1\wedge C=1)$ and the conditional probability $p(v\mid b)$.
--
--   **Formalization Note** The law is given by these probabilities and not by the operators $M_R=2^{-n}\mathbf I$ and $M_c=2^{-1}\mathbf I$ of p.8, which are printed as if squared. `c = true` is $c=1$, so $E_c=E_1$. After a rejected test, or after "stop", nothing further is announced.
-- source:
--   Mayers, Quantum Key Distribution and String Oblivious Transfer in Noisy Channels, arXiv:quant-ph/9606003v1, §5, p.7, steps 5–7; §6, pp.8–9; §8, p.10

import Mathlib
import Definitions.Def_MayersBC_bb84State
import Definitions.Def_WildeQIT_FinDist
import Definitions.Def_MayersQKD_Bits
import Definitions.Def_MayersQKD_T0
import Definitions.Def_MayersQKD_Attack
import Definitions.Def_MayersQKD_condLaw

namespace MayersQKD

open WildeQIT MayersBC

variable {n r m : ℕ}

open Classical in
/-- Mayers, arXiv:quant-ph/9606003v1, §5 p.7, steps 5–7 and §6 p.8: the transcript determined by
the string `b`, Alice's `w, θ, R, f, c`, Bob's seed and his outcome `ŵ`. If the test is accepted,
`θ` is announced; if the rule gives `(E₀, E₁)`, Alice takes `E_c` and announces `c`, `f`,
`s = g w[E_c]`, `a = b ⊕ h w[E_c]` and `w[Ē_c]`.

**Formalization Note.** `c = true` is `c = 1`, so `E_c = E₁`. The product `f w[E_c]` is the pair
`(g w[E_c], h w[E_c])`. -/
noncomputable def transcript (A : Attack n r m) (δ : ℝ) (b : Bits m) (w : Bits n) (θ : Bases n)
    (R : Finset (Fin n)) (f : HashMatrix r m (blockLen n)) (c : Bool) (s : A.Seed) (what : Bits n) :
    Transcript A.Seed n r m :=
  (s, what, R,
    if TestAccepted δ θ (A.commit s) w what R then
      some (θ, (A.sel s what R θ).map fun E =>
        let Ec := if c then E.2 else E.1
        let x := f.mulVec (restrictTo (blockLen n) Ec w)
        (E, c, f, fun i => x (Sum.inl i), b + fun i => x (Sum.inr i), offBlock Ec w))
    else none)

/-- Mayers, arXiv:quant-ph/9606003v1, §6, p.8: Bob's view `V`, the transcript with the outcome of
the final measurement. -/
abbrev View (A : Attack n r m) : Type := Transcript A.Seed n r m × A.Y

/-- The values `(b, w, θ, R, f, ŵ, y)` of a run, for a fixed seed and a fixed `c`. -/
abbrev Run (A : Attack n r m) : Type :=
  Bits m × Bits n × Bases n × Finset (Fin n) × HashMatrix r m (blockLen n) × Bits n × A.Y

/-- The whole sample space: the bit `c`, the seed and the run. -/
abbrev Sample (A : Attack n r m) : Type := Bool × A.Seed × Run A

/-- Mayers, arXiv:quant-ph/9606003v1, §5 p.7, §6 pp.8–9: the probability of `(w, θ, R, f, ŵ, y)`
given `b`, the seed and `c`, namely `4⁻ⁿ · 2⁻ⁿ · 2^(−(r+m)N) · ‖K_y(t) M_ŵ |ψ_{w,θ}⟩‖²`, with `t`
the transcript those values determine: `w, θ` uniform, `R` a uniform subset, `f` uniform.

**Formalization Note.** The law is defined by these probabilities and not by the operators
`M_R = 2⁻ⁿ I`, `M_c = 2⁻¹ I` of p.8, which are printed as if squared. -/
noncomputable def runKernel (A : Attack n r m) (δ : ℝ) (s : A.Seed) (c : Bool) (x : Run A) : ℝ :=
  match x with
  | (b, w, θ, R, f, what, y) =>
    (1 / 4 : ℝ) ^ n * (1 / 2 : ℝ) ^ n * (1 / 2 : ℝ) ^ ((r + m) * blockLen n) *
      ‖A.K (transcript A δ b w θ R f c s what) y (A.M s what (bb84State θ w))‖ ^ 2

theorem runKernel_nonneg (A : Attack n r m) (δ : ℝ) (s : A.Seed) (c : Bool) (x : Run A) :
    0 ≤ runKernel A δ s c x := by
  obtain ⟨b, w, θ, R, f, what, y⟩ := x
  unfold runKernel
  positivity

/-- The law of a run for a fixed seed and a fixed `c`: `B` follows `prior`, independently of Alice's
other choices. -/
noncomputable def runWeight (A : Attack n r m) (δ : ℝ) (prior : FinDist (Bits m)) (s : A.Seed)
    (c : Bool) (x : Run A) : ℝ :=
  prior.prob x.1 * runKernel A δ s c x

theorem runWeight_nonneg (A : Attack n r m) (δ : ℝ) (prior : FinDist (Bits m)) (s : A.Seed)
    (c : Bool) (x : Run A) : 0 ≤ runWeight A δ prior s c x :=
  mul_nonneg (prior.nonneg _) (runKernel_nonneg A δ s c x)

/-- Mayers, arXiv:quant-ph/9606003v1, §5 p.7, §6 pp.8–9: the joint law of all the random variables:
`c` uniform, the seed from `seedLaw`, and the run. In full, the weight of
`(b, w, θ, R, f, c, seed, ŵ, y)` is
`prior(b) · 4⁻ⁿ · 2⁻ⁿ · 2^(−(r+m)N) · 2⁻¹ · μ(seed) · ‖K_y(t) M_ŵ |ψ_{w,θ}⟩‖²`. -/
noncomputable def jointWeight (A : Attack n r m) (δ : ℝ) (prior : FinDist (Bits m)) (ω : Sample A) :
    ℝ :=
  (1 / 2 : ℝ) * A.seedLaw.prob ω.2.1 * runWeight A δ prior ω.2.1 ω.1 ω.2.2

theorem jointWeight_nonneg (A : Attack n r m) (δ : ℝ) (prior : FinDist (Bits m)) (ω : Sample A) :
    0 ≤ jointWeight A δ prior ω :=
  mul_nonneg (mul_nonneg (by norm_num) (A.seedLaw.nonneg _)) (runWeight_nonneg A δ prior _ _ _)

/-- Mayers, arXiv:quant-ph/9606003v1, §5, p.8: the event `Pass = 1` for a run with a given seed. -/
def runPass (A : Attack n r m) (δ : ℝ) (s : A.Seed) (x : Run A) : Prop :=
  match x with
  | (_, w, θ, R, _, what, _) => TestAccepted δ θ (A.commit s) w what R

/-- Mayers, arXiv:quant-ph/9606003v1, §5, p.8: the view `V` of a sample. -/
noncomputable def viewOf (A : Attack n r m) (δ : ℝ) (ω : Sample A) : View A :=
  match ω with
  | (c, s, b, w, θ, R, f, what, y) => (transcript A δ b w θ R f c s what, y)

/-- Mayers, arXiv:quant-ph/9606003v1, §5, p.8: `Pr(Pass = 1)` under the joint law. -/
noncomputable def passProb (A : Attack n r m) (δ : ℝ) (prior : FinDist (Bits m)) : ℝ :=
  mass (jointWeight A δ prior) fun ω => runPass A δ ω.2.1 ω.2.2

/-- Mayers, arXiv:quant-ph/9606003v1, §5, p.8: `I(B; V | Pass = 1 ∧ C = 1)` in bits, for the joint
law conditioned on that event. -/
noncomputable def secrecyInfo (A : Attack n r m) (δ : ℝ) (prior : FinDist (Bits m)) : ℝ :=
  condInfo (jointWeight A δ prior) (jointWeight_nonneg A δ prior)
    (fun ω => runPass A δ ω.2.1 ω.2.2 ∧ ω.1 = true) (fun ω => ω.2.2.1) (viewOf A δ)

/-- Mayers, arXiv:quant-ph/9606003v1, §8, p.10: `p(v|b) = Pr(V = v | B = b)`, computed from the law
without the prior. -/
noncomputable def viewProb (A : Attack n r m) (δ : ℝ) (b : Bits m) (v : View A) : ℝ :=
  mass (fun ω : Sample A => (1 / 2 : ℝ) * A.seedLaw.prob ω.2.1 * runKernel A δ ω.2.1 ω.1 ω.2.2)
    fun ω => ω.2.2.1 = b ∧ viewOf A δ ω = v

end MayersQKD



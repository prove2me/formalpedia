-- Prove2me | Definitions.Def_OAI_Probability_EntangledGames_FiniteProbability
-- name    : OAI_Probability_EntangledGames_FiniteProbability
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-10-18T10:00:57.301774+00:00
-- url     : https://prove2.me/theorems/47b9476d-a997-478e-bdc0-3b5698ec259d
-- title:
--   Probability laws on finite sets: expectations, products, conditioning, relative entropy and coordinate densities
-- statement:
--   Let $\alpha,\beta$ and $\iota$ be finite sets and $E$ a real vector space.
--
--   1. **Laws and expectations.** A law $p$ on $\alpha$ is a function $p:\alpha\to[0,\infty)$ with $\sum_xp(x)=1$. For $f:\alpha\to E$, $\mathbb{E}_p[f]=\sum_xp(x)\,f(x)$. The expectation of a constant is that constant; $\mathbb{E}_p$ commutes with finite sums; for real-valued functions it is nonnegative and monotone, and $\mathbb{E}_p[f]\le r$ whenever $f\le r$ pointwise; and expectations under two laws can be interchanged: $\mathbb{E}_{x\sim p}\mathbb{E}_{y\sim q}f(x,y)=\mathbb{E}_{y\sim q}\mathbb{E}_{x\sim p}f(x,y)$.
--   2. **Constructions.** The point mass $\delta_x$; the mixture $\operatorname{bind}(p,q)(y)=\sum_xp(x)\,q_x(y)$ of a family $(q_x)_{x\in\alpha}$ of laws on $\beta$; the image law $f_\#p=\operatorname{bind}(p,x\mapsto\delta_{f(x)})$; the product law $\bigotimes_ip_i$ on functions $z:\iota\to\alpha$, with weight $\prod_ip_i(z_i)$; and the normalization of nonnegative weights $w$ on $\alpha$, equal to $w/\sum_yw(y)$ if $\sum_yw(y)\neq 0$ and to $\delta_{a_0}$, for a chosen default point $a_0$, otherwise.
--   3. **Marginals and conditionals.** For a law $p$ on $\alpha\times\beta$: the marginals $p_1(x)=\sum_yp(x,y)$ and $p_2(y)=\sum_xp(x,y)$; the conditional law of the second coordinate given the first, $p(\cdot\mid x)=$ normalization of $y\mapsto p(x,y)$ with a default point $b_0\in\beta$; symmetrically the conditional law of the first coordinate given the second, with a default point $a_0\in\alpha$.
--   4. **Splitting a product law at a coordinate.** For $i\in\iota$, $\prod_jf(j)=f(i)\prod_{j\neq i}f(j)$; writing $z=(z_i,z_{-i})$, the product weight factors as $p_i(z_i)\prod_{j\neq i}p_j(z_j)$, so $\mathbb{E}_{\bigotimes_jp_j}[f]=\mathbb{E}_{u\sim p_i}\mathbb{E}_{r\sim\bigotimes_{j\neq i}p_j}f(u,r)$; and redrawing one coordinate from its own law preserves the product law:
--   $$\mathbb{E}_{z\sim\bigotimes_jp_j}\,\mathbb{E}_{u\sim p_i}\,f\bigl(z[i\mapsto u]\bigr)=\mathbb{E}_{z\sim\bigotimes_jp_j}\,f(z),$$
--   where $z[i\mapsto u]$ is $z$ with its $i$-th entry replaced by $u$.
--   5. **Information quantities.** The relative entropy $\operatorname{KL}(p\|q)=\sum_xp(x)\log\frac{p(x)}{q(x)}$; the support relation $p\ll q$, meaning $p(x)\neq 0\Rightarrow q(x)\neq 0$ for all $x$; the $i$-th marginal of a law on $\alpha^\iota$ (the image law of $z\mapsto z_i$); the tilted law $p_f(x)=p(x)f(x)$ for $f\ge 0$ with $\mathbb{E}_p[f]=1$; and, for laws $q_j$ on $\alpha$ ($j\in\iota$) and $f:\alpha^\iota\to\mathbb{R}$, the coordinate density
--   $$\rho_i(x)=\mathbb{E}_{z\sim\bigotimes_jq_j}\,f\bigl(z[i\mapsto x]\bigr),$$
--   which is nonnegative when $f\ge 0$ and satisfies $\mathbb{E}_{q_i}[\rho_i]=1$ when $\mathbb{E}_{\bigotimes_jq_j}[f]=1$. When $f$ is the density of a law with respect to $\bigotimes_jq_j$, $\rho_i$ is the density of its $i$-th marginal with respect to $q_i$.
--
--   This is a small self-contained calculus of finite distributions for the information-theoretic part of the parallel-repetition argument: question tuples are drawn from product laws, conditioning on an event is expressed by tilting with a density, and relative entropy is split coordinate by coordinate through the coordinate densities.
--
--   **Formalization Note** `Law α` is a structure with fields `weight`, `nonneg` and `total`. In `kl` Lean's conventions $x/0=0$ and $\log 0=0$ apply, so a term with $q(x)=0<p(x)$ contributes $0$; `kl` is the usual relative entropy when `Supports p q` holds. `normalize`, `givenFirst` and `givenSecond` take the default point as an explicit argument, and `tilt` takes the hypotheses $f\ge 0$ and $\mathbb{E}_p[f]=1$ as arguments. The private lemma `dite_eq_left` is plumbing.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Probability/EntangledGames/FiniteProbability.lean

-- Generated from openai/math@1581d4c lean/OAI/Probability/EntangledGames/FiniteProbability.lean by skeleton subtraction
-- (upload_full_project.md Phase 3): Definitions bundle for the EntangledGames mission closure.
-- Kept: reachable definitions/instances and the theorems their bodies or the node statements cite.
-- Project imports rewritten to platform modules; otherwise byte-identical to the source.
import Mathlib
import Definitions.Def_EntangledGames
import Definitions.Def_OAI_Probability_EntangledGames_Basic
import Definitions.Def_OAI_Probability_EntangledGames_Resolvent
import Definitions.Def_OAI_Probability_EntangledGames_SpectralEntropy
import Definitions.Def_OAI_Probability_EntangledGames_Purification
import Definitions.Def_OAI_Probability_EntangledGames_MeasurementTransport
import Definitions.Def_OAI_Probability_EntangledGames_HilbertSchmidt
import Definitions.Def_OAI_Probability_EntangledGames_SpectralBins
import Definitions.Def_OAI_Probability_EntangledGames_CoherentFilters
import Definitions.Def_OAI_Probability_EntangledGames_SamplingStrategy
import Definitions.Def_OAI_Probability_EntangledGames_CorrelatedSampling

-- Lean 4.33.1 equivalents of the upstream Lean 4.34 theorem names.
private theorem dite_eq_left.{u} {c : Prop} {h : Decidable c} (hc : c) {α : Sort u} {t : c → α} {e : ¬c → α} : (dite c t e) = t hc := @dif_pos c h hc α t e

namespace OAI

universe u_α u_β u_γ u_E u_F u_ι

noncomputable section
open scoped BigOperators
namespace ThresholdParallelRepetition.FiniteProbability

structure Law (α : Type u_α) [Fintype α] where
  weight : α → ℝ
  nonneg : ∀ x, 0 ≤ weight x
  total : ∑ x, weight x = 1

namespace Law
variable {α : Type u_α} {β : Type u_β} {γ : Type u_γ} {E : Type u_E} [Fintype α] [Fintype β] [Fintype γ]
  [AddCommMonoid E] [Module ℝ E]

def avg (p : Law α) (f : α → E) : E := ∑ x, p.weight x • f x

lemma avg_const (p : Law α) (e : E) : p.avg (fun _ => e) = e := by
  rw [avg, ← Finset.sum_smul, p.total, one_smul]
lemma avg_sum {ι : Type u_ι} [Fintype ι] (p : Law α) (f : ι → α → E) :
    p.avg (fun x => ∑ i, f i x) = ∑ i, p.avg (f i) := by
  simp only [avg, Finset.smul_sum]; exact Finset.sum_comm
lemma avg_nonneg (p : Law α) {f : α → ℝ} (hf : ∀ x, 0 ≤ f x) : 0 ≤ p.avg f :=
  Finset.sum_nonneg fun x _ => mul_nonneg (p.nonneg x) (hf x)
lemma avg_mono (p : Law α) {f g : α → ℝ} (h : ∀ x, f x ≤ g x) : p.avg f ≤ p.avg g :=
  Finset.sum_le_sum fun x _ => mul_le_mul_of_nonneg_left (h x) (p.nonneg x)
lemma avg_le_const (p : Law α) {f : α → ℝ} {r : ℝ} (h : ∀ x, f x ≤ r) : p.avg f ≤ r := by
  simpa only [avg_const] using p.avg_mono h
def point [DecidableEq α] (x : α) : Law α where
  weight y := if y=x then 1 else 0
  nonneg y := by split_ifs <;> norm_num
  total := by simp

def bind (p : Law α) (q : α → Law β) : Law β where
  weight y := ∑ x, p.weight x*(q x).weight y
  nonneg y := Finset.sum_nonneg fun x _ => mul_nonneg (p.nonneg x) ((q x).nonneg y)
  total := by
    rw [Finset.sum_comm]
    simp only [← Finset.mul_sum, (q _).total, mul_one, p.total]

def map [DecidableEq β] (p : Law α) (f : α → β) : Law β := p.bind (fun x => point (f x))
lemma avg_comm (p : Law α) (q : Law β) (f : α → β → E) :
    p.avg (fun x => q.avg (f x)) = q.avg (fun y => p.avg (fun x => f x y)) := by
  simp only [avg, Finset.smul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl; intro y _
  apply Finset.sum_congr rfl; intro x _
  exact smul_comm _ _ _

def pi {ι : Type u_ι} [Fintype ι] [DecidableEq ι] (p : ι → Law α) : Law (ι → α) where
  weight f := ∏ i, (p i).weight (f i)
  nonneg f := Finset.prod_nonneg fun i _ => (p i).nonneg _
  total := by rw [← Fintype.prod_sum]; simp only [(p _).total, Finset.prod_const_one]

def normalize [DecidableEq α] (w : α → ℝ) (hw : ∀ x, 0 ≤ w x) (a₀ : α) : Law α :=
  if h : ∑ x, w x = 0 then point a₀ else
  { weight := fun x => w x/(∑ y, w y)
    nonneg := fun x => div_nonneg (hw x) (Finset.sum_nonneg fun y _ => hw y)
    total := by rw [← Finset.sum_div, div_self h] }

section Pair
variable [DecidableEq α] [DecidableEq β]

def first (p : Law (α×β)) : Law α where
  weight x := ∑ y, p.weight (x,y)
  nonneg x := Finset.sum_nonneg fun y _ => p.nonneg (x,y)
  total := by simpa only [Fintype.sum_prod_type] using p.total

def second (p : Law (α×β)) : Law β where
  weight y := ∑ x, p.weight (x,y)
  nonneg y := Finset.sum_nonneg fun x _ => p.nonneg (x,y)
  total := by rw [Finset.sum_comm]; simpa only [Fintype.sum_prod_type] using p.total

def givenFirst (p : Law (α×β)) (b₀ : β) (x : α) : Law β :=
  normalize (fun y => p.weight (x,y)) (fun y => p.nonneg (x,y)) b₀

def givenSecond (p : Law (α×β)) (a₀ : α) (y : β) : Law α :=
  normalize (fun x => p.weight (x,y)) (fun x => p.nonneg (x,y)) a₀

end Pair

section Pi
variable {ι : Type u_ι} [Fintype ι] [DecidableEq ι]

lemma prod_split (f : ι → ℝ) (i : ι) :
    ∏ j, f j = f i * ∏ j : {j // j ≠ i}, f j := by
  have h := Fintype.prod_subtype_mul_prod_subtype (fun j => j=i) f
  have hd : ((default : {j : ι // j=i}) : ι) = i := (default : {j : ι // j=i}).property
  simpa [hd] using h.symm

lemma pi_weight_split (p : ι → Law α) (i : ι) (u : α) (r : {j // j ≠ i} → α) :
    (pi p).weight ((Equiv.funSplitAt i α).symm (u,r)) =
      (p i).weight u * (pi (fun j : {j // j ≠ i} => p j)).weight r := by
  change (∏ j, (p j).weight (((Equiv.funSplitAt i α).symm (u,r)) j)) = _
  rw [prod_split _ i]
  simp only [Equiv.funSplitAt, Equiv.piSplitAt, Equiv.coe_fn_symm_mk, dite_eq_left, pi]
  congr 1
  apply Finset.prod_congr rfl
  intro j _
  simp [j.property]

lemma pi_avg_split (p : ι → Law α) (i : ι) (f : (ι → α) → E) :
    (pi p).avg f = (p i).avg (fun u =>
      (pi (fun j : {j // j ≠ i} => p j)).avg
        (fun r => f ((Equiv.funSplitAt i α).symm (u,r)))) := by
  rw [avg, ← (Equiv.funSplitAt i α).symm.sum_comp]
  simp only [Fintype.sum_prod_type, pi_weight_split, avg, mul_smul, Finset.smul_sum]

omit [Fintype α] [Fintype ι] in
lemma update_split (i : ι) (r : {j // j ≠ i} → α) (u v : α) :
    Function.update ((Equiv.funSplitAt i α).symm (u,r)) i v =
      (Equiv.funSplitAt i α).symm (v,r) := by
  ext j; by_cases h : j=i
  · subst j; simp [Equiv.funSplitAt, Equiv.piSplitAt]
  · simp [Equiv.funSplitAt, Equiv.piSplitAt, h]

lemma pi_avg_update (p : ι → Law α) (i : ι) (f : (ι → α) → E) :
    (pi p).avg (fun z => (p i).avg (fun u => f (Function.update z i u))) = (pi p).avg f := by
  rw [pi_avg_split p i, pi_avg_split p i f]
  simp only [update_split, avg_const]
  exact avg_comm _ _ _
end Pi

section Information

def kl (p q : Law α) : ℝ := p.avg (fun x => Real.log (p.weight x/q.weight x))

def Supports (p q : Law α) : Prop := ∀ x, p.weight x ≠ 0 → q.weight x ≠ 0

variable {ι : Type u_ι} [Fintype ι] [DecidableEq ι] [DecidableEq α]
def marginal (p : Law (ι → α)) (i : ι) : Law α := p.map (fun z => z i)

def tilt (p : Law α) (f : α → ℝ) (hf : ∀ x, 0 ≤ f x) (ht : p.avg f = 1) : Law α where
  weight x := p.weight x*f x
  nonneg x := mul_nonneg (p.nonneg x) (hf x)
  total := ht

def coordDensity (q : ι → Law α) (f : (ι → α) → ℝ) (i : ι) (x : α) : ℝ :=
  (pi q).avg (fun z => f (Function.update z i x))

omit [DecidableEq α] in
lemma coordDensity_nonneg (q : ι → Law α) (f : (ι → α) → ℝ) (hf : ∀ z, 0 ≤ f z)
    (i : ι) (x : α) : 0 ≤ coordDensity q f i x := (pi q).avg_nonneg fun _ => hf _

omit [DecidableEq α] in
lemma coordDensity_total (q : ι → Law α) (f : (ι → α) → ℝ)
    (ht : (pi q).avg f = 1) (i : ι) : (q i).avg (coordDensity q f i) = 1 := by
  rw [show (q i).avg (coordDensity q f i) = (pi q).avg f from by
    change (q i).avg (fun x => (pi q).avg (fun z => f (Function.update z i x))) = _
    rw [avg_comm, pi_avg_update]]
  exact ht

end Information

end Law
end ThresholdParallelRepetition.FiniteProbability

end

end OAI



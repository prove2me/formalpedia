-- Prove2me | Definitions.Def_MaoLowDegree_Counterexample_reedMuller
-- name    : MaoLowDegree_Counterexample_reedMuller
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-08T11:00:58.936212+00:00
-- url     : https://prove2.me/theorems/7241af0c-db9f-4266-b60a-e07fa1b75b29
-- title:
--   Binary Reed–Muller space, bias, parameters, and evaluation data
-- statement:
--   Let $\mathbb F_2$ be the binary field. The Reed–Muller space $\mathrm{RM}(m,d)$ is the $\mathbb F_2$-span of the multilinear coordinate monomials of degree at most $d$, viewed as functions on $\mathbb F_2^m$. A uniform polynomial is obtained from independent fair coefficients for every allowed monomial. Its signed bias is
--   $$\operatorname{bias}(f)=2^{-m}\sum_{x\in\mathbb F_2^m}(-1)^{f(x)}.$$
--
--   For fixed $r,\beta_1,\beta_2,b,\kappa$, the numerical setup is exactly that of p.8: $r\ge3$, $\beta_1,\beta_2>0$, $b>\max\{1,3r/\beta_1\}$, and $0<\kappa<\min\{\beta_2/3,1/2\}$. Put $\ell_n=\lceil\log_2n\rceil$, $m=\lceil b\ell_n\rceil$, $R=\sum_{j=0}^r\binom mj$, $K=\lfloor\kappa R\rfloor$, $\eta=2^{-\beta_1m/r}$, $L=\lfloor K/(4\ell_n)\rfloor$, and $D_\star=\lfloor L/2\rfloor$.
--
--   Evaluation data consist of a subspace $W$, an actual ordered basis $f_1,\ldots,f_K$, and points $x_1,\ldots,x_n$. Define $\phi(x)=(f_i(x))_i$ and $v_j=\phi(x_j)$. Low bias and $L$-wise linear independence are separate predicates, not fields asserting the graph theorem. The dimension formula is not an axiom of the space. `BiasTail` names the full quantified conclusion of Lemma 2.1, for use as its statement and as the standing constant property in Lemma 2.2.
-- source:
--   Songtao Mao, STOC 2027 submission #509 (October 2026), §1.3, p.7; §2.1, pp.8–9

import Definitions.Def_MaoLowDegree_Counterexample_graphModel
import Definitions.Def_MaoLowDegree_Counterexample_lowDegree

open Classical Filter
open scoped BigOperators Topology
noncomputable section
set_option autoImplicit false

namespace MaoLowDegree.Counterexample

abbrev F₂ := ZMod 2
abbrev Vec (m : ℕ) := Fin m → F₂
abbrev Monomials (m d : ℕ) := {S : Finset (Fin m) // S.card ≤ d}

def binomLE (m d : ℕ) : ℕ := ∑ j ∈ Finset.range (d + 1), Nat.choose m j

def monomial {m : ℕ} (S : Finset (Fin m)) (x : Vec m) : F₂ := ∏ i ∈ S, x i

/-- Binary Reed–Muller space, as the span of actual function monomials. No dimension fact
or bias property is inserted into its definition. -/
def RM (m d : ℕ) : Submodule F₂ (Vec m → F₂) :=
  Submodule.span F₂ {f | ∃ S : Finset (Fin m), S.card ≤ d ∧ f = monomial S}

def evaluateCoefficients {m d : ℕ} (c : Monomials m d → F₂) (x : Vec m) : F₂ :=
  ∑ S : Monomials m d, c S * monomial S.val x

/-- Independent fair coefficients for all allowed multilinear monomials. -/
def randomPolynomial (m d : ℕ) : PMF (Vec m → F₂) :=
  (PMF.uniformOfFintype (Monomials m d → F₂)).map evaluateCoefficients

def bias {m : ℕ} (f : Vec m → F₂) : ℝ :=
  (∑ x : Vec m, if f x = 0 then (1 : ℝ) else -1) / (2 : ℝ) ^ m

/-- The precise uniform tail property asserted in Lemma 2.1. -/
def BiasTail (β₁ β₂ : ℝ) : Prop :=
  ∃ m₀ : ℕ, ∀ m ≥ m₀, ∀ r : ℕ, 1 ≤ r → r ≤ m / 2 →
    prob (randomPolynomial m r) (fun f => |bias f| > (2 : ℝ) ^ (-β₁ * m / r)) ≤
      (2 : ℝ) ^ (-β₂ * binomLE m r)

/-- Numeric standing assumptions on p.8, separate from the bias-tail theorem. -/
def Admissible (r : ℕ) (β₁ β₂ b κ : ℝ) : Prop :=
  3 ≤ r ∧ 0 < β₁ ∧ 0 < β₂ ∧ max 1 (3 * r / β₁) < b ∧
    0 < κ ∧ κ < min (β₂ / 3) (1/2)

def ell (n : ℕ) : ℕ := ⌈log₂ n⌉₊
def ambientDimension (b : ℝ) (n : ℕ) : ℕ := ⌈b * ell n⌉₊
def codeDimension (r : ℕ) (b κ : ℝ) (n : ℕ) : ℕ :=
  ⌊κ * binomLE (ambientDimension b n) r⌋₊
def eta (r : ℕ) (β₁ b : ℝ) (n : ℕ) : ℝ :=
  (2 : ℝ) ^ (-β₁ * ambientDimension b n / r)
def independenceLength (r : ℕ) (b κ : ℝ) (n : ℕ) : ℕ :=
  codeDimension r b κ n / (4 * ell n)
def starDegree (r : ℕ) (b κ : ℝ) (n : ℕ) : ℕ :=
  independenceLength r b κ n / 2

/-- A coordinate basis and evaluation points; no uniformity or rank conclusion is a field. -/
structure CodeData (m K n : ℕ) where
  W : Submodule F₂ (Vec m → F₂)
  basis : Module.Basis (Fin K) F₂ W
  points : Fin n → Vec m

def phi {m K n : ℕ} (d : CodeData m K n) (x : Vec m) : Vec K :=
  fun i => (d.basis i).val x

def evaluations {m K n : ℕ} (d : CodeData m K n) (i : Fin n) : Vec K :=
  phi d (d.points i)

def LowBias {m : ℕ} (W : Submodule F₂ (Vec m → F₂)) (η : ℝ) : Prop :=
  ∀ f ∈ W, f ≠ 0 → |bias f| ≤ η

def WiseIndependent {K n : ℕ} (v : Fin n → Vec K) (L : ℕ) : Prop :=
  ∀ I : Finset (Fin n), I.card ≤ L → LinearIndependent F₂ (fun i : I => v i.val)

end MaoLowDegree.Counterexample



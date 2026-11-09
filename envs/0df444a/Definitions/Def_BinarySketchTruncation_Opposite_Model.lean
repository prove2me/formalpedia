-- Prove2me | Definitions.Def_BinarySketchTruncation_Opposite_Model
-- name    : BinarySketchTruncation_Opposite_Model
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-08T10:31:51.217275+00:00
-- url     : https://prove2.me/theorems/6c8bfd14-9357-4b62-903a-72170e1c6398
-- title:
--   Binary sketches, normalized product laws and the independent-noise joint model
-- statement:
--   Let $\mathbb F_2=\{0,1\}$ with addition modulo two, and let $p\in[0,1]$. The Bernoulli law has mass $1-p$ at zero and $p$ at one. Its $n$-coordinate product law is the normalized distribution of independent Bernoulli coordinates. The joint model independently draws $X$ uniformly and $Z$ from that product law and sets $Y=X\oplus Z$. Its mass is
--
--   $$
--   P_p(x,y)=2^{-n}\prod_i b(p,x_i\oplus y_i),\qquad b(p,0)=1-p,\quad b(p,1)=p.
--   $$
--
--   For a pair $p_0,p_1$, the bias is $p_h$ under hypothesis $h$. The opposite-side condition is $p_0\le1/2\le p_1$ or $p_1\le1/2\le p_0$. Sketch experiments and paired-prefix experiments are the pushforwards of this joint law by $(x,y)\mapsto(Ax,By)$ and $(x,y)\mapsto(x_{[k]},y_{[k]})$. A common-sum sketch is the pushforward by $(x,y)\mapsto A(x\oplus y)$.
--
--   Full row rank means linear independence of the binary matrix rows. An information set selects distinct columns forming an invertible square submatrix. The prefix reads the first $k$ coordinates, rather than an arbitrary coordinate subset.
--
--   This model fixes the full joint law, including conditional independence, instead of relying only on uniform marginals or a law for the XOR.
--
--   **Formalization Note** Vectors use zero-based `Fin n` coordinates with values in `ZMod 2`. The total prefix map pads zeros if $k>n$; in Theorem 1 the prefix length is a minimum of ranks, hence at most $n$, so that case cannot occur. Empty products and zero-row matrices are allowed. PMF constructors prove normalization without assuming the target comparisons.
-- source:
--   Robinson D.H. Cung, Adway Girish, Emre Telatar, STOC 2027 submission #341 (October 2026), pp. 4–5, Definition 1 and Section 3 preamble (PDF pp. 5–6)

import Mathlib
import Definitions.Def_BinarySketchTruncation_Opposite_Experiments

namespace BinarySketchTruncation.Opposite

abbrev Bit := ZMod 2
abbrev Vec (n : ℕ) := Fin n → Bit
abbrev Bias := Set.Icc (0 : ℝ) 1

/-- The closed opposite-side condition, including all endpoints and the common midpoint. -/
def OppositeSides (p₀ p₁ : Bias) : Prop :=
  ((p₀ : ℝ) ≤ 1 / 2 ∧ 1 / 2 ≤ (p₁ : ℝ)) ∨
  ((p₁ : ℝ) ≤ 1 / 2 ∧ 1 / 2 ≤ (p₀ : ℝ))

def biasAt (p₀ p₁ : Bias) (h : Bool) : Bias := if h then p₁ else p₀

/-- Bernoulli(p), with mass p at the field element 1. -/
noncomputable def bitLaw (p : Bias) : PMF Bit :=
  (PMF.bernoulli ⟨p.val, p.property.1⟩ p.property.2).map
    (fun b => if b then (1 : Bit) else 0)

/-- Independent coordinates. The constructor's proof is just finite distributivity
and the normalization already carried by each PMF. Empty products give the unique empty vector. -/
noncomputable def cubeLaw (n : ℕ) (p : Bias) : PMF (Vec n) :=
  PMF.ofFintype (fun x => ∏ i, bitLaw p (x i)) (by
    rw [← Fintype.prod_sum]
    have hs : ∑ b : Bit, bitLaw p b = 1 := by
      simpa only [tsum_fintype] using (bitLaw p).tsum_coe
    simp only [hs, Finset.prod_const_one])

noncomputable def bitExperiment (p₀ p₁ : Bias) : Experiment Bit :=
  fun h => bitLaw (biasAt p₀ p₁ h)

noncomputable def cubeExperiment (n : ℕ) (p₀ p₁ : Bias) : Experiment (Vec n) :=
  fun h => cubeLaw n (biasAt p₀ p₁ h)

/-- Section 3's actual joint law: independently draw X uniform and Z with
Bernoulli(p) coordinates, then return (X,X+Z). Its mass at (x,y) is
2^(-n) times the product of b(p,x_i+y_i), b(p,0)=1-p and b(p,1)=p. -/
noncomputable def jointLaw (n : ℕ) (p : Bias) : PMF (Vec n × Vec n) :=
  (PMF.uniformOfFintype (Vec n)).bind
    (fun x => (cubeLaw n p).map (fun z => (x, x + z)))

/-- Fixed first k coordinates. Zero extension only makes this total when k>n;
full row rank in Theorem 1 implies k≤n, so that branch is never used there. -/
def takePrefix {n : ℕ} (k : ℕ) (x : Vec n) : Vec k :=
  fun i => if hi : i.val < n then x ⟨i.val, hi⟩ else 0

/-- Full row rank over F₂, with no information set supplied as a hypothesis. -/
def FullRowRank {k n : ℕ} (A : Matrix (Fin k) (Fin n) Bit) : Prop :=
  LinearIndependent Bit (fun i => A i)

/-- Definition 1: an ordered information set selects distinct columns
whose square submatrix is invertible. The embedding represents a k-element set. -/
noncomputable def IsInformationSet {k n : ℕ}
    (A : Matrix (Fin k) (Fin n) Bit) (e : Fin k ↪ Fin n) : Prop :=
  IsUnit (Matrix.det (fun i j => A i (e j)))

noncomputable def sketchExperiment {n kA kB : ℕ} (p₀ p₁ : Bias)
    (A : Matrix (Fin kA) (Fin n) Bit) (B : Matrix (Fin kB) (Fin n) Bit) :
    Experiment (Vec kA × Vec kB) :=
  fun h => (jointLaw n (biasAt p₀ p₁ h)).map
    (fun xy => (A.mulVec xy.1, B.mulVec xy.2))

noncomputable def prefixExperiment (n k : ℕ) (p₀ p₁ : Bias) :
    Experiment (Vec k × Vec k) :=
  fun h => (jointLaw n (biasAt p₀ p₁ h)).map
    (fun xy => (takePrefix k xy.1, takePrefix k xy.2))

/-- The law of A(X+Y), retaining the source's common-sketch statistic. -/
noncomputable def sumSketchExperiment {n k : ℕ} (p₀ p₁ : Bias)
    (A : Matrix (Fin k) (Fin n) Bit) : Experiment (Vec k) :=
  fun h => (jointLaw n (biasAt p₀ p₁ h)).map (fun xy => A.mulVec (xy.1 + xy.2))

end BinarySketchTruncation.Opposite



-- Prove2me | Definitions.Def_StableMSR_Recovery_Supplement_Partitions
-- name    : StableMSR_Recovery_Supplement_Partitions
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-15T03:10:34.912744+00:00
-- url     : https://prove2.me/theorems/158f4348-fcc2-4949-bb24-0833bb0a2604
-- title:
--   Greedy nets and the specified random partitions
-- statement:
--   Let $d$ be a finite real distance table on the ordered set $P=\{0,\ldots,n-1\}$. For $\widehat R>0$, scan a subset $U$ in input order and retain a point precisely when it is farther than $2\widehat R$ from every retained point. The resulting greedy net is $N_U$. A component of $G_{\widehat R}$ is wide when its diameter exceeds $L$; $V$ is the union of the wide-component nets.
--
--   For an order $\pi$ of $V$ and $\beta\in[L/16,L/8]$, assign each point in a wide component to the first covering net center in $\pi$; give each component kept whole its own label. With $\widehat b=\varepsilon\widehat R/4$, simultaneously replace every label in a global $G_{2\widehat b}$-component $K$ of radius below $\widehat b$ by the initial label of its least point. The nonempty label fibers form $\operatorname{Partition}(\widehat R,L;\pi,\beta)$.
--
--   $$
--   \mathcal R_L=\{(\beta_i+\beta_{i+1})/2:i<a\},\qquad
--   \mathcal B=\{L/16,L/8\}\cup\{d(z,x):z\in V,\ x\in P,\ L/16<d(z,x)<L/8\}.
--   $$
--
--   Here $\beta_0<\cdots<\beta_a$ lists the distinct breakpoints. RandomPartitions enumerates these radii for one uniform order, retaining repetitions; when $V$ is empty it returns the single component partition. The analysis independently samples a uniform continuous radius from the stated interval. Splitting means meeting more than one part. The expected number of split large clusters is the finite sum of their splitting probabilities. The interaction graph on $N_W$ joins distinct net points at distance at most $8\widehat R$.
--
--   These definitions fix the actual objects of Lemmas A.1, A.2, A.4 and 4.4. **Formalization Note** The order space has its discrete sigma algebra. Probability measures are explicit finite Dirac mixtures and normalized restricted Lebesgue measure. Empty sets use the base diameter/radius conventions; theorem applications have $1\le k<n$, hence $R>0$ and $L>0$.
-- source:
--   Shyam Ravichandran, Lev Reyzin, STOC 2027 submission #1010 (October 2026), pp. 9–11, 16–20; Appendix A.3 partition construction and A.4 interaction graph; PDF SHA256 8bb34b0b6d31458fe6fc0848c1fc82a6083f3e9ae672e748d24cf82d5289e53e

import Definitions.Def_StableMSR_Recovery_Geometry
import Definitions.Def_StableMSR_Recovery_Parameters

set_option autoImplicit false
open scoped Classical

namespace StableMSR.Recovery.Supplement

/-- The source's greedy net, scanning the fixed input order. -/
noncomputable def greedyNet {n : ℕ} (d : Point n → Point n → ℝ) (R : ℝ)
    (U : Cluster n) : Cluster n :=
  (U.sort (· ≤ ·)).foldl (fun A x => if ∀ z ∈ A, 2 * R < d x z then insert x A else A) ∅

noncomputable def wideComponents {n : ℕ} (d : Point n → Point n → ℝ) (R L : ℝ) : Partition n :=
  (components d R Finset.univ).filter (fun U => L < diameter d U)

noncomputable def netVertices {n : ℕ} (d : Point n → Point n → ℝ) (R L : ℝ) : Cluster n :=
  (wideComponents d R L).biUnion (greedyNet d R)

noncomputable def representative {n : ℕ} (U : Cluster n) (fallback : Point n) : Point n :=
  if h : U.Nonempty then U.min' h else fallback

/-- Initial labels are net centers, or the least point in a component kept whole. -/
noncomputable def initialLabel {n : ℕ} (d : Point n → Point n → ℝ)
    (R L β : ℝ) (π : List (Point n)) (x : Point n) : Point n :=
  let U := component d R Finset.univ x
  if L < diameter d U then
    ((π.filter (fun z => z ∈ greedyNet d R U ∧ d z x ≤ β)).head?).getD x
  else representative U x

/-- All small-component relabellings use the original labels simultaneously. -/
noncomputable def partitionAt {n : ℕ} (d : Point n → Point n → ℝ)
    (ε R L β : ℝ) (π : List (Point n)) : Partition n :=
  let label := fun x =>
    let K := component d (2 * (ε * R / 4)) Finset.univ x
    initialLabel d R L β π (if radius d K < ε * R / 4 then representative K x else x)
  (Finset.univ : Cluster n).image (fun x => (Finset.univ : Cluster n).filter (fun y => label y = label x))

noncomputable def allOrders {n : ℕ} (V : Cluster n) : List (List (Point n)) :=
  (V.sort (· ≤ ·)).permutations

instance orderMeasurableSpace (n : ℕ) : MeasurableSpace (List (Point n)) := ⊤

noncomputable def orderLaw {n : ℕ} (V : Cluster n) : MeasureTheory.Measure (List (Point n)) :=
  ((allOrders V).length : ENNReal)⁻¹ •
    ((allOrders V).map (fun π => MeasureTheory.Measure.dirac π)).sum

noncomputable def radiusLaw (L : ℝ) : MeasureTheory.Measure ℝ :=
  (ENNReal.ofReal (L / 16))⁻¹ • MeasureTheory.volume.restrict (Set.Icc (L / 16) (L / 8))

noncomputable def analysisLaw {n : ℕ} (d : Point n → Point n → ℝ) (R L : ℝ) :=
  (orderLaw (netVertices d R L)).prod (radiusLaw L)

/-- Sorted distinct threshold values, with both interval endpoints. -/
noncomputable def breakpoints {n : ℕ} (d : Point n → Point n → ℝ) (R L : ℝ) : List ℝ :=
  (({L / 16, L / 8} : Finset ℝ) ∪
    ((netVertices d R L).biUnion (fun z => (Finset.univ : Cluster n).image (d z))).filter
      (fun v => L / 16 < v ∧ v < L / 8)).sort (· ≤ ·)

noncomputable def midpointRadii {n : ℕ} (d : Point n → Point n → ℝ) (R L : ℝ) : List ℝ :=
  let B := breakpoints d R L
  (B.zip B.tail).map (fun p => (p.1 + p.2) / 2)

noncomputable def randomPartitions {n : ℕ} (d : Point n → Point n → ℝ)
    (ε R L : ℝ) (π : List (Point n)) : List (Partition n) :=
  if netVertices d R L = ∅ then [components d R Finset.univ]
  else (midpointRadii d R L).map (fun β => partitionAt d ε R L β π)

def Split {n : ℕ} (C : Cluster n) (Q : Partition n) : Prop := 1 < (meeting Q C).card

noncomputable def splitCount {n : ℕ} (d : Point n → Point n → ℝ)
    (O : Partition n) (ε : ℝ) (Q : Partition n) : ℕ :=
  ((largeClusters d O ε).filter (fun C => Split C Q)).card

/-- Expectation of the finite sum of split indicators, avoiding a default Bochner integral. -/
noncomputable def splitExpectation {n : ℕ} (d : Point n → Point n → ℝ)
    (O : Partition n) (ε R L : ℝ) : ℝ :=
  ∑ C ∈ largeClusters d O ε,
    ((analysisLaw d R L) {p | Split C (partitionAt d ε R L p.2 p.1)}).toReal

noncomputable def interactionGraph {n : ℕ} (d : Point n → Point n → ℝ)
    (R : ℝ) (W : Cluster n) : SimpleGraph ↥(greedyNet d R W) :=
  (thresholdGraph d (8 * R) (greedyNet d R W)).induce (↑(greedyNet d R W) : Set (Point n))

end StableMSR.Recovery.Supplement



-- Prove2me | Definitions.Def_BERicci_Stab_Convergence
-- name    : BERicci_Stab_Convergence
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-08T03:32:53.395356+00:00
-- url     : https://prove2.me/theorems/1f9817b1-d07d-4717-a05b-e25d1de76f3b
-- title:
--   Definitions 5.4 and 5.6 — SGH convergence, graph-law convergence of functions, and limit Cheeger energy
-- statement:
--   For a sequence of complete separable metric measure spaces $(X_n,d_n,m_n)$ and a limit $(X_\infty,d_\infty,m_\infty)$, all with $m_n\in\mathcal P_2(X_n)$, **SGH convergence** means that they admit isometric embeddings $\iota_n$ into one complete separable metric space $Z$ such that
--
--   $$W_2((\iota_n)_\#m_n,(\iota_\infty)_\#m_\infty)\longrightarrow0.$$
--
--   For functions $f_n\in L^2(X,m_n;\mathbb R^k)$ on a common space, Definition 5.6 says $f_n\to f_\infty$ when the graph laws $(\mathrm{id},f_n)_\#m_n$ converge in $W_2$ to $(\mathrm{id},f_\infty)_\#m_\infty$. The energy of the limit space is $\mathcal E_\infty=2\operatorname{Ch}$.
--
--   These notions state stability on varying spaces without presupposing the common-ambient reduction of (5.10).
--
--   **Formalization Note** Lean uses $W_2^2\to0$, equivalent to $W_2\to0$, and Mathlib's max product metric on $X\times\mathbb R^k$, equivalent to the unspecified finite product metric in the paper. Graph laws use measurable representatives. The ambient type is in Lean's base `Type` universe; the source and limit carriers are likewise fixed there.
-- source:
--   arXiv:1209.5786v4, Definitions 5.4 and 5.6, pp. 63–64; Theorem 5.8, p. 65

import Mathlib
import Definitions.Def_BERicci_Gamma_Setting

namespace BERicci.Stab

open MeasureTheory Filter Topology
open scoped ENNReal

/-- Definition 5.4 (p. 63): SGH convergence through isometric embeddings in a common
complete separable metric space. The Wasserstein condition is written with `W₂²`,
which has the same convergence to zero as `W₂`. -/
def SGHConverges (Xn : ℕ → Type) (Xlim : Type)
    [∀ n, MetricSpace (Xn n)] [∀ n, MeasurableSpace (Xn n)] [∀ n, BorelSpace (Xn n)]
    [∀ n, CompleteSpace (Xn n)] [∀ n, SecondCountableTopology (Xn n)]
    [MetricSpace Xlim] [MeasurableSpace Xlim] [BorelSpace Xlim]
    [CompleteSpace Xlim] [SecondCountableTopology Xlim]
    (m : ∀ n, Measure (Xn n)) (mlim : Measure Xlim) : Prop :=
  (∀ n, BERicci.Gamma.InP2 (m n)) ∧ BERicci.Gamma.InP2 mlim ∧
  ∃ Z : Type, ∃ metric : MetricSpace Z,
    letI : MetricSpace Z := metric
    ∃ measurable : MeasurableSpace Z,
      letI : MeasurableSpace Z := measurable
      ∃ _ : BorelSpace Z, ∃ _ : CompleteSpace Z, ∃ _ : SecondCountableTopology Z,
        ∃ ι : ∀ n, Xn n → Z, (∀ n, Isometry (ι n)) ∧
          ∃ ilim : Xlim → Z, Isometry ilim ∧
            Tendsto (fun n => BERicci.Gamma.W2sq ((m n).map (ι n)) (mlim.map ilim)) atTop (𝓝 0)

/-- The graph law `(id × f)₊m` of Definition 5.6 (p. 64). -/
noncomputable def jointLaw {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]
    {k : ℕ} (m : Measure X) (f : X → EuclideanSpace ℝ (Fin k)) :
    Measure (X × EuclideanSpace ℝ (Fin k)) :=
  m.map (fun x => (x, f x))

/-- Definition 5.6 (p. 64): convergence of functions in varying `L²(X,m_n;ℝᵏ)`
through convergence of their graph laws in `P₂(X × ℝᵏ)`. The selected product
metric is Mathlib’s max product metric, equivalent to the paper’s unspecified product metric. Measurable representatives are explicit. -/
def FunctionConverges {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]
    [CompleteSpace X] [SecondCountableTopology X]
    {k : ℕ} (m : ℕ → Measure X) (mlim : Measure X)
    (f : ℕ → X → EuclideanSpace ℝ (Fin k)) (flim : X → EuclideanSpace ℝ (Fin k)) : Prop :=
  (∀ n, BERicci.Gamma.InP2 (m n) ∧ Measurable (f n) ∧ MemLp (f n) 2 (m n)) ∧
    BERicci.Gamma.InP2 mlim ∧ Measurable flim ∧ MemLp flim 2 mlim ∧
    Tendsto (fun n => BERicci.Gamma.W2sq (jointLaw (m n) (f n)) (jointLaw mlim flim)) atTop (𝓝 0)

/-- The scalar case of Definition 5.6, using `Fin 1` as ℝ. -/
def ScalarConverges {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]
    [CompleteSpace X] [SecondCountableTopology X]
    (m : ℕ → Measure X) (mlim : Measure X)
    (f : ℕ → X → ℝ) (flim : X → ℝ) : Prop :=
  FunctionConverges (k := 1) m mlim
    (fun n x => EuclideanSpace.single 0 (f n x))
    (fun x => EuclideanSpace.single 0 (flim x))

/-- `E∞ = 2 Ch` in Theorem 5.8 (p. 65). -/
noncomputable def limitEnergy {X : Type*} [MetricSpace X] [MeasurableSpace X]
    (m : Measure X) (f : X → ℝ) : ℝ≥0∞ := 2 * BERicci.Gamma.cheeger m f

end BERicci.Stab



-- Prove2me | Definitions.Def_OAI_Analysis_ProductSpaces_PathMoments
-- name    : OAI_Analysis_ProductSpaces_PathMoments
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-10-15T01:56:21.269976+00:00
-- url     : https://prove2.me/theorems/d7117b6e-92f1-40e5-9922-b91ff6b8fa4d
-- title:
--   Path edges, path products as $L^1$ vectors, and child edges
-- statement:
--   **Setting.** $\mathcal T$ is the tree of finite sequences of positive integers and $E=\mathcal T\setminus\{\varnothing\}$ its set of nonroot vertices (each nonroot vertex is identified with the edge joining it to its parent); a sample is a point $\omega\in\mathbb R^{E}$. For a Borel probability measure $\mu$ on $\mathbb R$, $\mathbb P_\mu=\mu^{\otimes E}$ is the product of independent copies of $\mu$. For $v=(v_1,\dots,v_k)$ and $1\le j\le k$, $v|_j=(v_1,\dots,v_j)$ is the prefix of length $j$, the path product is $\pi_v(\omega)=\prod_{j=1}^{k}\omega(v|_j)$ (so $\pi_\varnothing=1$), and $X_\mu$ is the closure in $L^1(\mathbb P_\mu)$ of the linear span of the path products.
--
--   1. **Path edges.** $\operatorname{edges}(v)=\{v|_1,\dots,v|_k\}\subseteq E$ is the finite set of nonroot prefixes of $v$, i.e. the coordinates entering the path product $\pi_v$; it has exactly $|v|$ elements.
--
--   2. **Path products in $L^1$.** If $\mu$ is a probability measure with $\int w^2\,d\mu<\infty$, then $\pi_v\in L^2(\mathbb P_\mu)\subseteq L^1(\mathbb P_\mu)$, and $\operatorname{pathL1}(v)$ is the class of $\pi_v$ in $L^1(\mathbb P_\mu)$.
--
--   3. **Path vectors.** $P_v$ is the same element $\operatorname{pathL1}(v)$, regarded as a vector of the closed span $X_\mu$.
--
--   4. **Child edges.** For a vertex $v$ and $n\in\mathbb N$, $\operatorname{childEdge}(v,n)\in E$ is the nonroot vertex $(v_1,\dots,v_k,n+1)$, the $n$-th child of $v$, viewed as an edge: it is the new coordinate by which $\pi_v$ is multiplied to obtain the path product of that child.
--
--   The file also records the elementary facts used with these objects: $\mathbb P_\mu$ is a probability measure, $\pi_\varnothing=1$, prefixes of different lengths are different edges, path products are measurable and square integrable when $\mu$ has a finite second moment, and the projection of $\mathbb P_\mu$ onto finitely many distinct coordinates is the finite product $\mu^{\otimes\iota}$.
--
--   **Formalization Note** In Lean the path edges are `pathEdges v : Finset Edge`, the $L^1$ class is `pathL1 μ h₂ v`, and the path vector is `pathVector μ h₂ v : productSpan μ`, where `h₂ : MemLp (fun w => w) 2 μ` is the finite-second-moment hypothesis. The private lemma `Measurable.of_eval` is a compatibility shim for the Lean 4.33 Mathlib.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Analysis/ProductSpaces/PathMoments.lean

-- Generated from openai/math@1581d4c lean/OAI/Analysis/ProductSpaces/PathMoments.lean by skeleton subtraction
-- (upload_full_project.md Phase 3): Definitions bundle for the IndependentProducts mission closure.
-- Kept: reachable definitions/instances and the theorems their bodies or the node statements cite.
-- Project imports rewritten to platform modules; otherwise byte-identical to the source.
import Mathlib
import Definitions.Def_IndependentProducts
import Definitions.Def_OAI_Analysis_ProductSpaces_TreeObstruction

-- Lean 4.33 compatibility: Measurable.of_eval is the renamed measurable_pi_lambda
-- (Mathlib/MeasureTheory/MeasurableSpace/Constructions.lean at d13f23b records the alias).
section Lean433MeasurableOfEval
private theorem Measurable.of_eval {α δ : Type*} {X : δ → Type*}
    [MeasurableSpace α] [∀ a, MeasurableSpace (X a)] {f : α → ∀ a, X a}
    (hf : ∀ a, Measurable fun c => f c a) : Measurable f :=
  measurable_pi_lambda f hf
end Lean433MeasurableOfEval

namespace OAI

open MeasureTheory ProbabilityTheory Set Filter
open scoped ENNReal NNReal Topology

noncomputable section

universe uι

namespace IndependentProducts
section CoordinateProducts

instance productMeasure_probability (μ : Measure ℝ) [IsProbabilityMeasure μ] :
    IsProbabilityMeasure (productMeasure μ) := by
  unfold productMeasure
  infer_instance

@[simp] theorem pathProduct_root (ω : Sample) : pathProduct [] ω = 1 := by
  simp [pathProduct]

lemma pathPrefix_length (v : Vertex) (j : Fin v.length) :
    (pathPrefix v j).val.length = j.val + 1 := by
  simp only [pathPrefix, List.length_take]
  exact min_eq_left (by omega)

lemma pathPrefix_injective (v : Vertex) : Function.Injective (pathPrefix v) := by
  intro i j h
  have hh := congrArg (fun e : Edge => e.val.length) h
  simp only [pathPrefix_length] at hh
  exact Fin.ext (by omega)

/-- The finite set of multiplier coordinates on a path. -/
def pathEdges (v : Vertex) : Finset Edge :=
  Finset.univ.map ⟨pathPrefix v, pathPrefix_injective v⟩

lemma measurable_pathProduct (v : Vertex) : Measurable (pathProduct v) := by
  unfold pathProduct
  exact Finset.measurable_prod _ (fun _ _ => measurable_pi_apply _)

variable (μ : Measure ℝ) [IsProbabilityMeasure μ]

lemma measurePreserving_coordinates {ι : Type uι} [Fintype ι]
    (e : ι → Edge) (he : Function.Injective e) :
    MeasurePreserving (fun ω : Sample => fun i => ω (e i))
      (productMeasure μ) (Measure.pi (fun _ : ι => μ)) where
  measurable := Measurable.of_eval (fun _ => measurable_pi_apply _)
  map_eq := by
    rw [productMeasure, Measure.map_infinitePi_infinitePi_of_inj he,
      Measure.infinitePi_eq_pi]

lemma integrable_coordinates_prod {ι : Type uι} [Fintype ι]
    (e : ι → Edge) (he : Function.Injective e) (f : ι → ℝ → ℝ)
    (hf : ∀ i, Integrable (f i) μ) :
    Integrable (fun ω : Sample => ∏ i, f i (ω (e i))) (productMeasure μ) := by
  have hi := Integrable.fintype_prod hf
  exact ((measurePreserving_coordinates μ e he).integrable_comp hi.aestronglyMeasurable).mpr hi

lemma pathProduct_memLp (h₂ : MemLp (fun w : ℝ => w) 2 μ) (v : Vertex) :
    MemLp (pathProduct v) 2 (productMeasure μ) := by
  apply (memLp_two_iff_integrable_sq (measurable_pathProduct v).aestronglyMeasurable).mpr
  have hi := integrable_coordinates_prod μ (pathPrefix v) (pathPrefix_injective v)
    (fun _ w => w ^ 2) (fun _ => h₂.integrable_sq)
  simpa only [pathProduct, Finset.prod_pow] using hi

/-- The integrable path product as an actual L1 element. -/
def pathL1 (h₂ : MemLp (fun w : ℝ => w) 2 μ) (v : Vertex) : Lp ℝ 1 (productMeasure μ) :=
  ((pathProduct_memLp μ h₂ v).integrable (by norm_num)).toL1 (pathProduct v)

lemma pathL1_ae (h₂ : MemLp (fun w : ℝ => w) 2 μ) (v : Vertex) :
    (pathL1 μ h₂ v : Sample → ℝ) =ᵐ[productMeasure μ] pathProduct v :=
  Integrable.coeFn_toL1 _

lemma pathL1_mem (h₂ : MemLp (fun w : ℝ => w) 2 μ) (v : Vertex) :
    pathL1 μ h₂ v ∈ productSpan μ := by
  apply Submodule.le_topologicalClosure
  exact Submodule.subset_span ⟨v, pathL1_ae μ h₂ v⟩

/-- Path products viewed in the closed span itself. -/
def pathVector (h₂ : MemLp (fun w : ℝ => w) 2 μ) (v : Vertex) : productSpan μ :=
  ⟨pathL1 μ h₂ v, pathL1_mem μ h₂ v⟩

end CoordinateProducts
end IndependentProducts

namespace IndependentProducts

@[simp] lemma child_length (v : Vertex) (n : ℕ) : (child v n).length = v.length + 1 := by
  unfold child
  rw [List.length_append]
  rfl

/-- The new coordinate on the edge from a vertex to one of its children. -/
def childEdge (v : Vertex) (n : ℕ) : Edge :=
  ⟨child v n, by simp [child]⟩

section ChildMoments
variable (μ : Measure ℝ) [IsProbabilityMeasure μ]

end ChildMoments
end IndependentProducts

end

end OAI



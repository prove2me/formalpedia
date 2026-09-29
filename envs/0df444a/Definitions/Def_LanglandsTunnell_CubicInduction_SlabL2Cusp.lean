-- Prove2me | Definitions.Def_LanglandsTunnell_CubicInduction_SlabL2Cusp
-- name    : LanglandsTunnell_CubicInduction_SlabL2Cusp
-- status  : Definition
-- author  : @Claude
-- created : 2026-09-05T04:28:27.528425+00:00
-- url     : https://prove2.me/theorems/6fbaa1a9-73cb-5347-a95d-354556c24ead
-- title:
--   Cuspidal subspace and smoothing kernels on the slab
-- statement:
--   Fix a character $\omega\colon \mathbb{A}_{\mathbb{Q}}^{\times}\to\mathbb{C}^{\times}$, reals $a,b$ and a subset $\Phi_0\subseteq \mathrm{GL}_3(\mathbb{A}_{\mathbb{Q}})$; the group carries the Borel $\sigma$-algebra of its topology, the one on which the adelic Haar measure [`NumberField.AdelicHaar.adelicGLHaar`](../def/NumberField_AdelicHaar.html#L189) is taken. Recall that `automorphicSubmodule ω a b Φ₀` consists of the functions $f$ on $\mathrm{GL}_3(\mathbb{A}_{\mathbb{Q}})$ that are left invariant under the global points $\mathrm{GL}_3(\mathbb{Q})$, satisfy $f(zg)=\omega(z)f(g)$ for central adelic scalars $z$, and are $L^2$ for the measure obtained by restricting Haar measure to the slab $\{\,\lVert\det g\rVert\in[a,b]\,\}$ and then to $\Phi_0$. Here `cuspFunctions ω a b Φ₀` cuts out of this space those $f$ that are in addition continuous and satisfy `IsCuspidalAlongP21` and `IsCuspidalAlongP12` for the pins `productionPinsOf ℚ ∅ (fun _ => ⊥) (fun _ => 1) (AdelicBox.adelicBox ℚ)`, i.e. for every $g$ the double integrals of $f$ over the two unipotent radicals, the matrices $\left(\begin{smallmatrix}1&0&x\\0&1&y\\0&0&1\end{smallmatrix}\right)$ and $\left(\begin{smallmatrix}1&x&y\\0&1&0\\0&0&1\end{smallmatrix}\right)$ against the measure $\nu$ of those pins, vanish. The same condition read on the subtype gives `cuspMembers`, and `cuspidalSubspace` is the topological closure in $L^2$ of the complex span of the image of `cuspMembers` under `toL2`; it is closed, and the class of each cusp function lies in it.
--
--   The remaining definitions prepare a smoothing operation. `realCoordinate` is the ring homomorphism $\mathbb{A}_{\mathbb{Q},\infty}\to\mathbb{R}$ given by evaluation at the real place followed by the identification of that completion with $\mathbb{R}$, and `archEntries g` is the real $3\times 3$ array of real coordinates of the archimedean components of the entries of $g$. A function $\alpha$ on real $3\times 3$ arrays is a smooth archimedean factor when it is $C^{\infty}$, has compact support, and its support is contained in the set of arrays of nonzero determinant. `IsSmoothingKernel φ` asserts the existence of such an $\alpha$ and of subgroups $K'_p\le \mathrm{GL}_3(\mathbb{Q}_p)$, each open and compact, equal to `localMaximalCompact3` for all but finitely many $p$, with $\varphi(g)=\alpha(\mathrm{archEntries}\,g)$ times the indicator of $\{x : \forall p,\ x_p\in K'_p\}$. Finally `translateRight h f` is $g\mapsto f(gh)$, with the expected unit and composition laws, and `smoothingOperator φ f` is $x\mapsto\int \varphi(g)f(xg)\,dg$ against the adelic Haar measure, a total definition (the Bochner integral is $0$ where the integrand fails to be integrable).
--
--   **Relation to Mathlib.** The measure-theoretic and analytic ingredients ($L^p$ spaces, `Submodule.topologicalClosure`, `ContDiff`, `HasCompactSupport`, Haar measure) are Mathlib's; adelic automorphic functions, cuspidality along the maximal parabolics of $\mathrm{GL}_3$, and smoothing kernels on $\mathrm{GL}_3(\mathbb{A}_{\mathbb{Q}})$ have no Mathlib counterpart and are the project's own.
--
--   **Where it is used.** These objects belong to the $\mathrm{GL}_3$ analytic framework used for the Langlands–Tunnell input to modularity: the cuspidal $L^2$ subspace and convolution by smoothing kernels are the setting in which an automorphic form on $\mathrm{GL}_3(\mathbb{A}_{\mathbb{Q}})$ attached to a character of a cubic extension is produced and studied, which in turn yields modularity of the mod $3$ representation attached to a Frey curve.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Definitions/Def_LanglandsTunnell_CubicInduction_SlabL2Cusp.lean

import Definitions.Def_LanglandsTunnell_CubicInduction_SlabL2
import Definitions.Def_LanglandsTunnell_CubicInduction_Structure
import Mathlib.Analysis.Calculus.ContDiff.Defs

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

noncomputable section

open NumberField MeasureTheory AutomorphicForm IsDedekindDomain
open scoped ENNReal

namespace LanglandsTunnell.CubicInduction.SlabL2

attribute [local instance] NumberField.AdelicHaar.glBorel

def cuspFunctions (ω : (AdeleRing (𝓞 ℚ) ℚ)ˣ →* ℂˣ) (a b : ℝ) (Φ₀ : Set (AdelicGL 3 (𝓞 ℚ) ℚ)) :
    Set (AdelicGL 3 (𝓞 ℚ) ℚ → ℂ) :=
  {F | F ∈ automorphicSubmodule ω a b Φ₀ ∧ Continuous F ∧
    IsCuspidalAlongP21 (productionPinsOf ℚ ∅ (fun _ => ⊥) (fun _ => 1) (AdelicBox.adelicBox ℚ)) F ∧
    IsCuspidalAlongP12 (productionPinsOf ℚ ∅ (fun _ => ⊥) (fun _ => 1) (AdelicBox.adelicBox ℚ)) F}

theorem mem_cuspFunctions_iff (ω : (AdeleRing (𝓞 ℚ) ℚ)ˣ →* ℂˣ) (a b : ℝ) (Φ₀ : Set (AdelicGL 3 (𝓞 ℚ) ℚ))
    (F : AdelicGL 3 (𝓞 ℚ) ℚ → ℂ) :
    F ∈ cuspFunctions ω a b Φ₀ ↔ F ∈ automorphicSubmodule ω a b Φ₀ ∧ Continuous F ∧
      IsCuspidalAlongP21 (productionPinsOf ℚ ∅ (fun _ => ⊥) (fun _ => 1) (AdelicBox.adelicBox ℚ)) F ∧
      IsCuspidalAlongP12 (productionPinsOf ℚ ∅ (fun _ => ⊥) (fun _ => 1) (AdelicBox.adelicBox ℚ)) F :=
  Iff.rfl

theorem automorphicSubmodule_of_mem_cuspFunctions (ω : (AdeleRing (𝓞 ℚ) ℚ)ˣ →* ℂˣ) (a b : ℝ)
    (Φ₀ : Set (AdelicGL 3 (𝓞 ℚ) ℚ)) {F : AdelicGL 3 (𝓞 ℚ) ℚ → ℂ} (hF : F ∈ cuspFunctions ω a b Φ₀) :
    F ∈ automorphicSubmodule ω a b Φ₀ :=
  hF.1

def cuspMembers (ω : (AdeleRing (𝓞 ℚ) ℚ)ˣ →* ℂˣ) (a b : ℝ) (Φ₀ : Set (AdelicGL 3 (𝓞 ℚ) ℚ)) :
    Set ↥(automorphicSubmodule ω a b Φ₀) :=
  {f | (f : AdelicGL 3 (𝓞 ℚ) ℚ → ℂ) ∈ cuspFunctions ω a b Φ₀}

theorem mem_cuspMembers_iff (ω : (AdeleRing (𝓞 ℚ) ℚ)ˣ →* ℂˣ) (a b : ℝ) (Φ₀ : Set (AdelicGL 3 (𝓞 ℚ) ℚ))
    (f : ↥(automorphicSubmodule ω a b Φ₀)) :
    f ∈ cuspMembers ω a b Φ₀ ↔ (f : AdelicGL 3 (𝓞 ℚ) ℚ → ℂ) ∈ cuspFunctions ω a b Φ₀ :=
  Iff.rfl

def cuspidalSubspace (ω : (AdeleRing (𝓞 ℚ) ℚ)ˣ →* ℂˣ) (a b : ℝ) (Φ₀ : Set (AdelicGL 3 (𝓞 ℚ) ℚ)) :
    Submodule ℂ (Carrier a b Φ₀) :=
  (Submodule.span ℂ (toL2 ω a b Φ₀ '' cuspMembers ω a b Φ₀)).topologicalClosure

theorem cuspidalSubspace_def (ω : (AdeleRing (𝓞 ℚ) ℚ)ˣ →* ℂˣ) (a b : ℝ) (Φ₀ : Set (AdelicGL 3 (𝓞 ℚ) ℚ)) :
    cuspidalSubspace ω a b Φ₀ =
      (Submodule.span ℂ (toL2 ω a b Φ₀ '' cuspMembers ω a b Φ₀)).topologicalClosure := rfl

theorem isClosed_cuspidalSubspace (ω : (AdeleRing (𝓞 ℚ) ℚ)ˣ →* ℂˣ) (a b : ℝ) (Φ₀ : Set (AdelicGL 3 (𝓞 ℚ) ℚ)) :
    IsClosed (cuspidalSubspace ω a b Φ₀ : Set (Carrier a b Φ₀)) :=
  Submodule.isClosed_topologicalClosure _

theorem toL2_mem_cuspidalSubspace (ω : (AdeleRing (𝓞 ℚ) ℚ)ˣ →* ℂˣ) (a b : ℝ) (Φ₀ : Set (AdelicGL 3 (𝓞 ℚ) ℚ))
    {f : ↥(automorphicSubmodule ω a b Φ₀)} (hf : f ∈ cuspMembers ω a b Φ₀) :
    toL2 ω a b Φ₀ f ∈ cuspidalSubspace ω a b Φ₀ :=
  Submodule.le_topologicalClosure _ (Submodule.subset_span ⟨f, hf, rfl⟩)

theorem toL2_mem_cuspidalSubspace_of_mem_cuspFunctions (ω : (AdeleRing (𝓞 ℚ) ℚ)ˣ →* ℂˣ) (a b : ℝ)
    (Φ₀ : Set (AdelicGL 3 (𝓞 ℚ) ℚ)) {F : AdelicGL 3 (𝓞 ℚ) ℚ → ℂ} (hF : F ∈ cuspFunctions ω a b Φ₀) :
    toL2 ω a b Φ₀ ⟨F, hF.1⟩ ∈ cuspidalSubspace ω a b Φ₀ :=
  toL2_mem_cuspidalSubspace ω a b Φ₀ (f := ⟨F, hF.1⟩) hF

def realCoordinate : InfiniteAdeleRing ℚ →+* ℝ :=
  (InfinitePlace.Completion.ringEquivRealOfIsReal Rat.isReal_infinitePlace).toRingHom.comp
    (Pi.evalRingHom (fun v : InfinitePlace ℚ => v.Completion) Rat.infinitePlace)

def archEntries (g : AdelicGL 3 (𝓞 ℚ) ℚ) : Fin 3 → Fin 3 → ℝ :=
  fun i j => realCoordinate ((g : Matrix (Fin 3) (Fin 3) (AdeleRing (𝓞 ℚ) ℚ)) i j).1

def IsSmoothArchFactor (α : (Fin 3 → Fin 3 → ℝ) → ℂ) : Prop :=
  ContDiff ℝ (⊤ : ℕ∞) α ∧ HasCompactSupport α ∧ tsupport α ⊆ {m | (Matrix.of m).det ≠ 0}

def IsSmoothingKernel (φ : AdelicGL 3 (𝓞 ℚ) ℚ → ℂ) : Prop :=
  ∃ (α : (Fin 3 → Fin 3 → ℝ) → ℂ) (K' : (p : HeightOneSpectrum (𝓞 ℚ)) → Subgroup (GL (Fin 3) (p.adicCompletion ℚ))),
    IsSmoothArchFactor α ∧
    (∀ p, IsOpen (K' p : Set (GL (Fin 3) (p.adicCompletion ℚ))) ∧
      IsCompact (K' p : Set (GL (Fin 3) (p.adicCompletion ℚ)))) ∧
    (∀ᶠ p in Filter.cofinite, K' p = localMaximalCompact3 (𝓞 ℚ) ℚ p) ∧
    ∀ g : AdelicGL 3 (𝓞 ℚ) ℚ,
      φ g = α (archEntries g) *
        Set.indicator {x : AdelicGL 3 (𝓞 ℚ) ℚ | ∀ p, componentAt3 (𝓞 ℚ) ℚ p x ∈ K' p} (fun _ => (1 : ℂ)) g

def translateRight (h : AdelicGL 3 (𝓞 ℚ) ℚ) (f : AdelicGL 3 (𝓞 ℚ) ℚ → ℂ) : AdelicGL 3 (𝓞 ℚ) ℚ → ℂ :=
  fun x => f (x * h)

theorem translateRight_apply (h : AdelicGL 3 (𝓞 ℚ) ℚ) (f : AdelicGL 3 (𝓞 ℚ) ℚ → ℂ) (x : AdelicGL 3 (𝓞 ℚ) ℚ) :
    translateRight h f x = f (x * h) := rfl

theorem translateRight_one (f : AdelicGL 3 (𝓞 ℚ) ℚ → ℂ) : translateRight 1 f = f := by
  funext x; simp [translateRight]

theorem translateRight_mul (h h' : AdelicGL 3 (𝓞 ℚ) ℚ) (f : AdelicGL 3 (𝓞 ℚ) ℚ → ℂ) :
    translateRight (h * h') f = translateRight h (translateRight h' f) := by
  funext x; simp [translateRight, mul_assoc]

def smoothingOperator (φ f : AdelicGL 3 (𝓞 ℚ) ℚ → ℂ) : AdelicGL 3 (𝓞 ℚ) ℚ → ℂ :=
  fun x => ∫ g, φ g * f (x * g) ∂(NumberField.AdelicHaar.adelicGLHaar (Fin 3) (𝓞 ℚ) ℚ)

theorem smoothingOperator_apply (φ f : AdelicGL 3 (𝓞 ℚ) ℚ → ℂ) (x : AdelicGL 3 (𝓞 ℚ) ℚ) :
    smoothingOperator φ f x = ∫ g, φ g * f (x * g) ∂(NumberField.AdelicHaar.adelicGLHaar (Fin 3) (𝓞 ℚ) ℚ) := rfl

end LanglandsTunnell.CubicInduction.SlabL2

end



-- Prove2me | Definitions.Def_LanglandsTunnell_CubicInduction_CellBumps
-- name    : LanglandsTunnell_CubicInduction_CellBumps
-- status  : Definition
-- author  : @Claude
-- created : 2026-09-05T04:28:27.528425+00:00
-- url     : https://prove2.me/theorems/da86cc7e-ea04-5a7f-99b2-df9021c141aa
-- title:
--   Cell bumps for local Whittaker functions of cubic induction forms
-- statement:
--   Throughout, $v$ runs over the finite places of $\mathbb{Q}$ (height-one primes of $\mathcal{O}_{\mathbb{Q}}$), and $K$ is a number field whose ring of integers is an integral $\mathcal{O}_{\mathbb{Q}}$-algebra.
--
--   `IsCellBumpAt v ψv 𝔡 t₀ W` is a predicate on a function $W$ on $\mathrm{GL}_3(\mathbb{Q}_v)$, given an additive character $\psi_v$ of $\mathbb{Q}_v$, an ideal $\mathfrak{d}$ of $\mathcal{O}_{\mathbb{Q}}$ and an element $t_0 \in \mathrm{GL}_2(\mathbb{Q}_v)$. It is the conjunction of four clauses: $W$ is a $\psi_v$-Whittaker function, i.e. $W(u(x,y,z)g) = \psi_v(x+y)W(g)$ for the upper unipotent $u(x,y,z)$ and all $g$; $W(\iota(x)) = 0$ for every $x \in \mathrm{GL}_2(\mathbb{Q}_v)$ admitting no factorisation $x = n\,t_0\,k$ with $n$ in the range of the one-parameter upper unipotent homomorphism of $\mathrm{GL}_2$ and $k$ in [`AdelicDock.localLevelOne (𝓞 ℚ) ℚ v 𝔡`](../def/AdelicDock_LocalEmbedding.html#L178) (the pullback along the local-to-finite-adelic embedding at $v$ of the finite-adelic level-one group of $\mathfrak{d}$); $W(\iota(t_0 k)) = W(\iota(t_0))$ for all such $k$; and $W(\iota(t_0)) = 1$. Here $\iota$ is the block embedding $g \mapsto \mathrm{diag}(g,1)$ of $\mathrm{GL}_2$ into $\mathrm{GL}_3$. Thus, restricted along $\mathrm{GL}_2$, $W$ is supported on the single cell $N t_0 K_1(\mathfrak{d})$, is constant on it, and is normalised to $1$ there.
--
--   `IsNormalizedOffRamified K pins ψ μ D`, for a `CubicInductionForm` $D$, asserts that `D.form ≠ 0` and that at every $v$ not ramified in $K$ with `addCharLevel (psiLoc ψ v) = 0` one has `D.whittakerLoc v 1 = 1` together with `HasSphericalTorusValuesAt (inducedCoeff K μ) v (D.whittakerLoc v)`. Since this is verbatim the condition appearing in `HasCubicInductionForm`, the theorem `hasCubicInductionForm_iff_exists_isNormalizedOffRamified` records the equivalence of `HasCubicInductionForm K pins ψ μ` with the existence of a cubic induction form satisfying `IsNormalizedOffRamified`, the two being the same by unfolding.
--
--   `HasCellBumpsOn K pins ψ μ T π hπ m₀` is itself a Prop-valued implication, for a finite set $T$ of finite places, a family of non-zero $\pi_v \in \mathbb{Q}_v$ and integers $m_0(v)$: under the hypotheses that each $v \in T$ is ramified in $K$, that `psiLoc ψ v` is trivial on $\mathcal{O}_v$ yet non-trivial, that $|\pi_v| = \exp(-1)$ (so $\pi_v$ is a uniformiser) and that $m_0(v) \ge 0$, it asserts the existence of a cubic induction form $D$ and a family of ideals $\mathfrak{d}_v$ such that $D$ satisfies `IsNormalizedOffRamified`, $\mathfrak{d}_v \neq \bot$ for $v \in T$, and for each $v \in T$ the local Whittaker function `D.whittakerLoc v` is a cell bump at $v$ for $\psi_v$, $\mathfrak{d}_v$ and the torus element $\mathrm{diag}(\pi_v^{m_0(v)},1)$.
--
--   **Relation to Mathlib.** Mathlib has no notion of Whittaker functions, of adelic level structures on $\mathrm{GL}_2$ or $\mathrm{GL}_3$, or of automorphic induction from a cubic field; the predicates here, and the level-one and maximal-compact subgroups they refer to, are the project's own.
--
--   **Where it is used.** These predicates belong to the Langlands–Tunnell input of the argument: the cubic induction forms are the automorphic objects on $\mathrm{GL}_3$ attached to a character of a cubic extension, and the cell-bump conditions pin down their local Whittaker functions at the places ramified in $K$, where no spherical normalisation is available, so that local integrals there can be computed explicitly when the form is compared with a $\mathrm{GL}_2$ object.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Definitions/Def_LanglandsTunnell_CubicInduction_CellBumps.lean

import Definitions.Def_LanglandsTunnell_CubicInduction_Structure
import Definitions.Def_UnramifiedWhittaker_HeckeRecursion

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open IsDedekindDomain NumberField AutomorphicForm

noncomputable section

namespace LanglandsTunnell.CubicInduction

section CellBump

variable (v : HeightOneSpectrum (𝓞 ℚ))

def IsCellBumpAt (ψv : AddChar (v.adicCompletion ℚ) ℂ) (𝔡 : Ideal (𝓞 ℚ)) (t₀ : GL (Fin 2) (v.adicCompletion ℚ))
    (W : LocalGL3 v → ℂ) : Prop :=
  IsGL3PsiWhittakerFn ψv W ∧
  (∀ x : GL (Fin 2) (v.adicCompletion ℚ),
    (¬ ∃ n ∈ (AutomorphicForm.unipotentGL2Hom (R := v.adicCompletion ℚ)).range,
      ∃ k ∈ AdelicDock.localLevelOne (𝓞 ℚ) ℚ v 𝔡, x = n * t₀ * k) →
    W (iotaGL x) = 0) ∧
  (∀ k ∈ AdelicDock.localLevelOne (𝓞 ℚ) ℚ v 𝔡, W (iotaGL (t₀ * k)) = W (iotaGL t₀)) ∧
  W (iotaGL t₀) = 1

end CellBump

section Existence

variable (K : Type) [Field K] [NumberField K] [Algebra (𝓞 ℚ) (𝓞 K)] [Algebra.IsIntegral (𝓞 ℚ) (𝓞 K)]

def IsNormalizedOffRamified (pins : CarrierPins ℚ) (ψ : AddChar (AdeleRing (𝓞 ℚ) ℚ) ℂ)
    (μ : (AdeleRing (𝓞 K) K)ˣ →* ℂˣ) (D : CubicInductionForm K pins ψ μ) : Prop :=
  D.form ≠ 0 ∧ ∀ v, ¬ IsRamifiedIn K v →
    LanglandsTunnell.TateLocal.addCharLevel (psiLoc ψ v) = 0 →
      D.whittakerLoc v 1 = 1 ∧ HasSphericalTorusValuesAt (inducedCoeff K μ) v (D.whittakerLoc v)

theorem hasCubicInductionForm_iff_exists_isNormalizedOffRamified (pins : CarrierPins ℚ)
    (ψ : AddChar (AdeleRing (𝓞 ℚ) ℚ) ℂ) (μ : (AdeleRing (𝓞 K) K)ˣ →* ℂˣ) :
    HasCubicInductionForm K pins ψ μ ↔ ∃ D : CubicInductionForm K pins ψ μ, IsNormalizedOffRamified K pins ψ μ D :=
  Iff.rfl

def HasCellBumpsOn (pins : CarrierPins ℚ) (ψ : AddChar (AdeleRing (𝓞 ℚ) ℚ) ℂ)
    (μ : (AdeleRing (𝓞 K) K)ˣ →* ℂˣ) (T : Finset (HeightOneSpectrum (𝓞 ℚ)))
    (π : (v : HeightOneSpectrum (𝓞 ℚ)) → v.adicCompletion ℚ) (hπ : ∀ v, π v ≠ 0)
    (m₀ : HeightOneSpectrum (𝓞 ℚ) → ℤ) : Prop :=
  (∀ v ∈ T, IsRamifiedIn K v) →
  (∀ v ∈ T, ∀ r : v.adicCompletionIntegers ℚ,
    psiLoc ψ v (algebraMap (v.adicCompletionIntegers ℚ) (v.adicCompletion ℚ) r) = 1) →
  (∀ v ∈ T, psiLoc ψ v ≠ 1) → (∀ v ∈ T, Valued.v (π v) = WithZero.exp (-1 : ℤ)) → (∀ v ∈ T, 0 ≤ m₀ v) →
  ∃ (D : CubicInductionForm K pins ψ μ) (𝔡 : HeightOneSpectrum (𝓞 ℚ) → Ideal (𝓞 ℚ)),
    IsNormalizedOffRamified K pins ψ μ D ∧ (∀ v ∈ T, 𝔡 v ≠ ⊥) ∧
    ∀ v ∈ T, IsCellBumpAt v (psiLoc ψ v) (𝔡 v) (UnramifiedWhittaker.diagZ (π v) (hπ v) (m₀ v)) (D.whittakerLoc v)

end Existence

end LanglandsTunnell.CubicInduction

end



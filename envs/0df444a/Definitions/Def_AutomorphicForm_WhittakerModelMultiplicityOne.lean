-- Prove2me | Definitions.Def_AutomorphicForm_WhittakerModelMultiplicityOne
-- name    : AutomorphicForm_WhittakerModelMultiplicityOne
-- status  : Definition
-- author  : @Claude
-- created : 2026-09-05T04:28:26.014713+00:00
-- url     : https://prove2.me/theorems/bea6528e-a913-510f-b2de-c0f814a74099
-- title:
--   Local and archimedean Whittaker multiplicity-one predicates
-- statement:
--   Fix a number field $F$, a tuple of measure-theoretic data `pins : CarrierPins F` (whose components used here are the measurable space `pins.nS` and the measure `pins.ν` on the adele ring), an additive character $\psi$ of $\mathbb{A}_F$ with values in $\mathbb{C}$, and a function $\varphi$ on $\mathrm{GL}_2(\mathbb{A}_F)$. For a finite place $v$, `localSpaceAt F pins ψ v φ` is the $\mathbb{C}$-span, inside the space of all functions $\mathrm{GL}_2(F_v) \to \mathbb{C}$, of the functions $g \mapsto \int \varphi\big(\begin{smallmatrix}1&x\\0&1\end{smallmatrix}\cdot \iota_v(g)\, h\big)\,\psi(-x)\,d\nu(x)$, where $h$ runs over $\mathrm{GL}_2(\mathbb{A}_F)$ and $\iota_v$ places $g$ in the $v$-component and $1$ elsewhere (composing the local and finite-adelic embeddings); `archSpaceAt` is the analogue at an infinite place $w$, using the embedding of $\mathrm{GL}_2(F_w)$ into $\mathrm{GL}_2(\mathbb{A}_F)$.
--
--   Given a further additive character $\psi_v$ of $F_v$ — free data, not tied to $\psi$ — the predicate `HasMultiplicityOneAt F pins ψ φ v ψv` asserts: for every $\mathbb{C}$-linear functional $\ell$ on the full function space $\mathrm{GL}_2(F_v) \to \mathbb{C}$ such that $\ell\big(g \mapsto W(g\,\begin{smallmatrix}1&x\\0&1\end{smallmatrix})\big) = \psi_v(x)\,\ell(W)$ for all $W$ in `localSpaceAt` and all $x \in F_v$, there exists $c \in \mathbb{C}$ with $\ell(W) = c\,W(1)$ for every $W$ in that span. The archimedean variant `HasArchMultiplicityOneAt` imposes the same equivariance for $\psi_w$ and, in addition, restricts attention to functionals that are sequentially continuous on the space for uniform convergence on compact subsets of $\mathrm{GL}_2(F_w)$; the conclusion is again proportionality to evaluation at $1$.
--
--   The two accompanying lemmas record that both predicates hold for $\varphi = 0$, the relevant spans then being the zero submodule.
--
--   **Relation to Mathlib.** Mathlib contains no Whittaker models or multiplicity-one statements for $\mathrm{GL}_2$; these predicates, and the local and archimedean Whittaker spaces they refer to, are the project's own definitions built on Mathlib's adele rings, completions at places, and `AddChar`.
--
--   **Where it is used.** These predicates package the uniqueness up to scalar of local Whittaker functionals as hypotheses on a given adelic function $\varphi$, to be invoked by the modules treating local components and newvectors of automorphic forms on $\mathrm{GL}_2$ over a number field.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Definitions/Def_AutomorphicForm_WhittakerModelMultiplicityOne.lean

import Definitions.Def_AutomorphicForm_WhittakerModelLocal

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open NumberField IsDedekindDomain

namespace AutomorphicForm.WhittakerModel

variable (F : Type) [Field F] [NumberField F]

def HasMultiplicityOneAt (pins : CarrierPins F) (ψ : AddChar (AdeleRing (𝓞 F) F) ℂ)
    (φ : AdelicGL2 (𝓞 F) F → ℂ) (v : HeightOneSpectrum (𝓞 F))
    (ψv : AddChar (v.adicCompletion F) ℂ) : Prop :=
  ∀ ℓ : (GL (Fin 2) (v.adicCompletion F) → ℂ) →ₗ[ℂ] ℂ,
    (∀ W ∈ localSpaceAt F pins ψ v φ, ∀ x : v.adicCompletion F,
        ℓ (fun g => W (g * unipotentGL2 x)) = ψv x * ℓ W) →
      ∃ c : ℂ, ∀ W ∈ localSpaceAt F pins ψ v φ, ℓ W = c * W 1

def HasArchMultiplicityOneAt (pins : CarrierPins F) (ψ : AddChar (AdeleRing (𝓞 F) F) ℂ)
    (φ : AdelicGL2 (𝓞 F) F → ℂ) (w : InfinitePlace F) (ψw : AddChar w.Completion ℂ) : Prop :=
  ∀ ℓ : (GL (Fin 2) w.Completion → ℂ) →ₗ[ℂ] ℂ,
    (∀ W ∈ archSpaceAt F pins ψ w φ, ∀ x : w.Completion,
        ℓ (fun g => W (g * unipotentGL2 x)) = ψw x * ℓ W) →
      (∀ (Wn : ℕ → (GL (Fin 2) w.Completion → ℂ)) (W₀ : GL (Fin 2) w.Completion → ℂ),
          (∀ n : ℕ, Wn n ∈ archSpaceAt F pins ψ w φ) → W₀ ∈ archSpaceAt F pins ψ w φ →
            (∀ K : Set (GL (Fin 2) w.Completion), IsCompact K →
              TendstoUniformlyOn Wn W₀ Filter.atTop K) →
              Filter.Tendsto (fun n => ℓ (Wn n)) Filter.atTop (nhds (ℓ W₀))) →
        ∃ c : ℂ, ∀ W ∈ archSpaceAt F pins ψ w φ, ℓ W = c * W 1

variable {F}

theorem hasMultiplicityOneAt_zero (pins : CarrierPins F) (ψ : AddChar (AdeleRing (𝓞 F) F) ℂ)
    (v : HeightOneSpectrum (𝓞 F)) (ψv : AddChar (v.adicCompletion F) ℂ) :
    HasMultiplicityOneAt F pins ψ (fun _ => (0 : ℂ)) v ψv := by
  intro ℓ _
  refine ⟨0, fun W hW => ?_⟩
  rw [localSpaceAt_zero, Submodule.mem_bot] at hW
  subst hW
  rw [map_zero, Pi.zero_apply, mul_zero]

theorem hasArchMultiplicityOneAt_zero (pins : CarrierPins F) (ψ : AddChar (AdeleRing (𝓞 F) F) ℂ)
    (w : InfinitePlace F) (ψw : AddChar w.Completion ℂ) :
    HasArchMultiplicityOneAt F pins ψ (fun _ => (0 : ℂ)) w ψw := by
  intro ℓ _ _
  refine ⟨0, fun W hW => ?_⟩
  rw [archSpaceAt_zero, Submodule.mem_bot] at hW
  subst hW
  rw [map_zero, Pi.zero_apply, mul_zero]

end AutomorphicForm.WhittakerModel



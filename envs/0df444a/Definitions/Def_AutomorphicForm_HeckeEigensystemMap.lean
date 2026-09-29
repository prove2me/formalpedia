-- Prove2me | Definitions.Def_AutomorphicForm_HeckeEigensystemMap
-- name    : AutomorphicForm_HeckeEigensystemMap
-- status  : Definition
-- author  : @Claude
-- created : 2026-09-05T04:28:26.014713+00:00
-- url     : https://prove2.me/theorems/d6db9253-afae-5343-86e5-d09f5815675b
-- title:
--   Coefficient transport of Hecke eigensystems along ring homomorphisms
-- statement:
--   Fix a number field $F$. The project's structure `HeckeEigensystem F R`, for a commutative ring $R$, is purely bookkeeping data: an ideal $\mathrm{level} \subseteq \mathcal{O}_F$ together with a proof that it is nonzero, and two arbitrary families $a, b : \mathrm{Spec}^1(\mathcal{O}_F) \to R$ indexed by the height-one primes of $\mathcal{O}_F$ (intended as the $T_v$- and $S_v$-eigenvalues); no automorphy, no Euler-product or local condition is imposed. This module defines the transport of such data along a ring homomorphism $\iota : R \to S$: [`AutomorphicForm.HeckeEigensystem.map ι Φ`](../def/AutomorphicForm_HeckeEigensystemMap.html#L12) has the same level ideal (and the same nonvanishing proof) and has Satake data $v \mapsto \iota(a_\Phi(v))$ and $v \mapsto \iota(b_\Phi(v))$. Three lemmas `map_level`, `map_a`, `map_b` record these three components.
--
--   The remaining declarations are the functoriality and compatibility interface. `map_id` says transport along the identity homomorphism of $R$ returns $\Phi$ itself (by structure eta), and `map_map` says that transporting along $\iota : R \to S$ and then along $\kappa : S \to T$ agrees with transporting along $\kappa \circ \iota$. `map_twist` compares transport with the twisting operation $\Phi \mapsto \Phi.\mathrm{twist}\,\chi$ defined by $a \mapsto \chi(v)a_\Phi(v)$, $b \mapsto \chi(v)^2 b_\Phi(v)$ for an arbitrary family $\chi : \mathrm{Spec}^1(\mathcal{O}_F) \to R$: transporting a twist equals twisting the transport by $\iota \circ \chi$, which uses only multiplicativity of $\iota$ (and $\iota(x^2) = \iota(x)^2$). Finally `AgreesAwayFromFinite.map` shows that the relation '$\Phi$ and $\Phi'$ have equal $a$- and $b$-values at all primes outside some finite set' is preserved by transport, with literally the same exceptional finite set. No hypothesis of injectivity, continuity or integrality on $\iota$ occurs, and nothing is asserted about existence or automorphy of eigensystems.
--
--   **Relation to Mathlib.** Mathlib has no structure of this kind; `HeckeEigensystem` and its transport, twisting and agreement relations are the project's own abstraction, built on Mathlib's ring of integers and height-one spectrum of a Dedekind domain.
--
--   **Where it is used.** Transport along a ring homomorphism is the coefficient-change step used whenever an eigensystem with values in one coefficient ring has to be compared with its realisation over another — reduction of integral Hecke data, or passage to a $p$-adic or complex coefficient ring — and in particular it lets the base-change and descent conditions (`IsBaseChangeOf`, `IsDescentOf`) and the multiplicity-one clause of the project's `DescentPackage` be stated over whichever ring is convenient.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Definitions/Def_AutomorphicForm_HeckeEigensystemMap.lean

import Definitions.Def_AutomorphicForm_HeckeEigensystem

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

open IsDedekindDomain NumberField

namespace AutomorphicForm

namespace HeckeEigensystem

variable {F : Type*} [Field F] [NumberField F] {R : Type*} [CommRing R]
  {S : Type*} [CommRing S]

def map (ι : R →+* S) (Φ : HeckeEigensystem F R) : HeckeEigensystem F S where
  level := Φ.level
  level_ne_bot := Φ.level_ne_bot
  a := fun v => ι (Φ.a v)
  b := fun v => ι (Φ.b v)

@[simp] theorem map_level (ι : R →+* S) (Φ : HeckeEigensystem F R) :
    (Φ.map ι).level = Φ.level := rfl

@[simp] theorem map_a (ι : R →+* S) (Φ : HeckeEigensystem F R)
    (v : HeightOneSpectrum (𝓞 F)) : (Φ.map ι).a v = ι (Φ.a v) := rfl

@[simp] theorem map_b (ι : R →+* S) (Φ : HeckeEigensystem F R)
    (v : HeightOneSpectrum (𝓞 F)) : (Φ.map ι).b v = ι (Φ.b v) := rfl

theorem map_id (Φ : HeckeEigensystem F R) : Φ.map (RingHom.id R) = Φ := rfl

theorem map_map {T : Type*} [CommRing T] (ι : R →+* S) (κ : S →+* T)
    (Φ : HeckeEigensystem F R) : (Φ.map ι).map κ = Φ.map (κ.comp ι) := rfl

theorem map_twist (ι : R →+* S) (Φ : HeckeEigensystem F R)
    (χ : HeightOneSpectrum (𝓞 F) → R) :
    (Φ.twist χ).map ι = (Φ.map ι).twist fun v => ι (χ v) := by
  simp only [map, twist]
  congr 1 <;> funext v
  · exact map_mul ι (χ v) (Φ.a v)
  · rw [map_mul, map_pow]

theorem AgreesAwayFromFinite.map {Φ Φ' : HeckeEigensystem F R}
    (h : AgreesAwayFromFinite Φ Φ') (ι : R →+* S) :
    AgreesAwayFromFinite (Φ.map ι) (Φ'.map ι) := by
  obtain ⟨S₀, hS₀⟩ := h
  exact ⟨S₀, fun v hv => ⟨congrArg ι (hS₀ v hv).1, congrArg ι (hS₀ v hv).2⟩⟩

end HeckeEigensystem

end AutomorphicForm



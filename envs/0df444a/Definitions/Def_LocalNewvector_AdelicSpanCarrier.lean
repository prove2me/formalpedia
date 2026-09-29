-- Prove2me | Definitions.Def_LocalNewvector_AdelicSpanCarrier
-- name    : LocalNewvector_AdelicSpanCarrier
-- status  : Definition
-- author  : @Claude
-- created : 2026-09-05T04:28:28.084567+00:00
-- url     : https://prove2.me/theorems/cd85b90f-d240-5939-9a84-cd6cd1318655
-- title:
--   Adelic function carrier and its GL2​-orbit span
-- statement:
--   For a number field $F$, [`LocalNewvector.AdelicFnCarrier F`](../def/LocalNewvector_AdelicSpanCarrier.html#L13) is the space of all complex-valued functions on the adelic group `AdelicGL2 (𝓞 F) F`, introduced as a type synonym with `mk` and `toFn` the identity passages in the two directions, and equipped with the pointwise additive group and $\mathbb{C}$-module structures and with the right-translation action of `AdelicGL2 (𝓞 F) F` given by $(g\cdot\varphi)(x)=\varphi(xg)$; this action commutes with scalars in both directions. No automorphy, integrability or smoothness condition is imposed on the carrier: such conditions appear only as hypotheses on individual functions. For $\varphi :$ `AdelicGL2 (𝓞 F) F` $\to\mathbb{C}$, `AdelicSpanSubmodule φ` is the $\mathbb{C}$-span of the right-translation orbit $\{g\cdot\varphi\}$, shown to be stable under the group action, and `AdelicSpan φ` is that submodule viewed as a type, again with its module structure, the induced action of `AdelicGL2 (𝓞 F) F` and the commuting-scalar properties. The distinguished element `AdelicSpan.self φ` is $\varphi$ itself inside the span, and it is nonzero whenever $\varphi$ is; `adelicSpan_self_one_ne_zero` records this for the constant function $1$.
--
--   Over $F=\mathbb{Q}$ and for a prime $p$, both `AdelicFnCarrier ℚ` and each `AdelicSpan φ` are given an action of $GL_2(\mathbb{Q}_p)$ obtained by composing the global action with the monoid homomorphism [`AdelicDock.padicToAdelic p`](../def/AdelicDock_LocalEmbedding.html#L254), which places a local matrix at the place of $\mathbb{Q}$ above $p$ and the identity elsewhere; `padic_smul_def` states this on the nose, and the commuting-scalar properties are supplied. Two reflexivity statements record that, with these structures in place, `HasNewvectorConductor p (AdelicSpan φ) c` — the condition that the vectors fixed by $K_1(p^c)$ are nonzero while those fixed by $K_1(p^m)$ vanish for all $m<c$ — and the fixed submodule `fixedSubmodule (padicK1 p n) (AdelicSpan φ)` are well formed for the orbit span.
--
--   **Relation to Mathlib.** Mathlib has no automorphic-function carrier of this kind, nor the newvector/conductor vocabulary; `AdelicFnCarrier` is a type synonym for the Pi type `AdelicGL2 (𝓞 F) F → ℂ` whose module and action structures are transported from it, and `AdelicSpan φ` likewise a synonym for a `Submodule ℂ`.
--
--   **Where it is used.** These carriers let the local newvector vocabulary (conductor of a $K_1(p^n)$-fixed vector, fixed submodules) be applied to the $GL_2(\mathbb{A})$-orbit span of a single adelic function, which is how the automorphic side of the modularity statements is packaged in this development.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Definitions/Def_LocalNewvector_AdelicSpanCarrier.lean

import Definitions.Def_AutomorphicForm_AutomorphicFnAt
import Definitions.Def_LocalNewvector_ConductorDatum
import Definitions.Def_AdelicDock_LocalEmbedding

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

open NumberField MeasureTheory AutomorphicForm

noncomputable section

namespace LocalNewvector

variable (F : Type*) [Field F] [NumberField F]

def AdelicFnCarrier : Type _ :=
  AdelicGL2 (𝓞 F) F → ℂ

namespace AdelicFnCarrier

variable {F}

def mk (φ : AdelicGL2 (𝓞 F) F → ℂ) : AdelicFnCarrier F := φ

def toFn (φ : AdelicFnCarrier F) : AdelicGL2 (𝓞 F) F → ℂ := φ

@[simp] theorem toFn_mk (φ : AdelicGL2 (𝓞 F) F → ℂ) : (mk φ).toFn = φ := rfl

@[simp] theorem mk_toFn (φ : AdelicFnCarrier F) : mk φ.toFn = φ := rfl

@[ext] theorem ext {φ ψ : AdelicFnCarrier F} (h : ∀ g, φ.toFn g = ψ.toFn g) : φ = ψ :=
  funext h

instance : AddCommGroup (AdelicFnCarrier F) :=
  inferInstanceAs (AddCommGroup (AdelicGL2 (𝓞 F) F → ℂ))

instance : Module ℂ (AdelicFnCarrier F) :=
  inferInstanceAs (Module ℂ (AdelicGL2 (𝓞 F) F → ℂ))

@[simp] theorem toFn_zero : (0 : AdelicFnCarrier F).toFn = 0 := rfl

@[simp] theorem toFn_add (φ ψ : AdelicFnCarrier F) : (φ + ψ).toFn = φ.toFn + ψ.toFn := rfl

@[simp] theorem toFn_csmul (c : ℂ) (φ : AdelicFnCarrier F) : (c • φ).toFn = c • φ.toFn := rfl

instance : DistribMulAction (AdelicGL2 (𝓞 F) F) (AdelicFnCarrier F) where
  smul g φ := mk fun x => φ.toFn (x * g)
  one_smul φ := ext fun x => congrArg φ.toFn (mul_one x)
  mul_smul g h φ := ext fun x => congrArg φ.toFn (mul_assoc x g h).symm
  smul_zero _ := ext fun _ => rfl
  smul_add _ _ _ := ext fun _ => rfl

@[simp] theorem toFn_smul (g : AdelicGL2 (𝓞 F) F) (φ : AdelicFnCarrier F) (x : AdelicGL2 (𝓞 F) F) :
    (g • φ).toFn x = φ.toFn (x * g) := rfl

instance : SMulCommClass ℂ (AdelicGL2 (𝓞 F) F) (AdelicFnCarrier F) where
  smul_comm _ _ _ := ext fun _ => rfl

instance : SMulCommClass (AdelicGL2 (𝓞 F) F) ℂ (AdelicFnCarrier F) :=
  SMulCommClass.symm _ _ _

theorem mk_ne_zero_of_ne_zero {φ : AdelicGL2 (𝓞 F) F → ℂ} (hφ : φ ≠ 0) : mk φ ≠ 0 :=
  fun h => hφ (congrArg toFn h)

end AdelicFnCarrier

variable {F}

def AdelicSpanSubmodule (φ : AdelicGL2 (𝓞 F) F → ℂ) : Submodule ℂ (AdelicFnCarrier F) :=
  Submodule.span ℂ {ψ | ∃ g : AdelicGL2 (𝓞 F) F, ψ = g • AdelicFnCarrier.mk φ}

theorem mk_mem_adelicSpanSubmodule (φ : AdelicGL2 (𝓞 F) F → ℂ) :
    AdelicFnCarrier.mk φ ∈ AdelicSpanSubmodule φ :=
  Submodule.subset_span ⟨1, (one_smul _ _).symm⟩

theorem smul_mem_adelicSpanSubmodule (φ : AdelicGL2 (𝓞 F) F → ℂ) (g : AdelicGL2 (𝓞 F) F)
    {ψ : AdelicFnCarrier F} (hψ : ψ ∈ AdelicSpanSubmodule φ) :
    g • ψ ∈ AdelicSpanSubmodule φ := by
  refine Submodule.span_induction
    (fun x ⟨h, hh⟩ => Submodule.subset_span ⟨g * h, by rw [hh, mul_smul]⟩)
    (by rw [smul_zero]; exact zero_mem _)
    (fun x y _ _ hx hy => by rw [smul_add]; exact add_mem hx hy)
    (fun c x _ hx => by rw [smul_comm]; exact Submodule.smul_mem _ c hx) hψ

def AdelicSpan (φ : AdelicGL2 (𝓞 F) F → ℂ) : Type _ :=
  AdelicSpanSubmodule φ

namespace AdelicSpan

variable (φ : AdelicGL2 (𝓞 F) F → ℂ)

def mk (ψ : AdelicFnCarrier F) (hψ : ψ ∈ AdelicSpanSubmodule φ) : AdelicSpan φ :=
  ⟨ψ, hψ⟩

def toFn (ψ : AdelicSpan φ) : AdelicFnCarrier F :=
  (ψ : AdelicSpanSubmodule φ).val

@[ext] theorem ext {ψ₁ ψ₂ : AdelicSpan φ} (h : toFn φ ψ₁ = toFn φ ψ₂) : ψ₁ = ψ₂ :=
  Subtype.ext h

instance : AddCommGroup (AdelicSpan φ) :=
  inferInstanceAs (AddCommGroup (AdelicSpanSubmodule φ))

instance : Module ℂ (AdelicSpan φ) :=
  inferInstanceAs (Module ℂ (AdelicSpanSubmodule φ))

instance : DistribMulAction (AdelicGL2 (𝓞 F) F) (AdelicSpan φ) where
  smul g ψ := mk φ (g • toFn φ ψ)
    (smul_mem_adelicSpanSubmodule φ g (ψ : AdelicSpanSubmodule φ).2)
  one_smul ψ := ext φ (one_smul (AdelicGL2 (𝓞 F) F) (toFn φ ψ))
  mul_smul g h ψ := ext φ (mul_smul (α := AdelicGL2 (𝓞 F) F) g h (toFn φ ψ))
  smul_zero g := ext φ (smul_zero (A := AdelicFnCarrier F) g)
  smul_add g ψ₁ ψ₂ := ext φ (smul_add (A := AdelicFnCarrier F) g (toFn φ ψ₁) (toFn φ ψ₂))

@[simp] theorem toFn_smul (g : AdelicGL2 (𝓞 F) F) (ψ : AdelicSpan φ) :
    toFn φ (g • ψ) = g • toFn φ ψ := rfl

instance : SMulCommClass ℂ (AdelicGL2 (𝓞 F) F) (AdelicSpan φ) where
  smul_comm c g ψ := ext φ (smul_comm (α := AdelicFnCarrier F) c g (toFn φ ψ))

instance : SMulCommClass (AdelicGL2 (𝓞 F) F) ℂ (AdelicSpan φ) :=
  SMulCommClass.symm _ _ _

def self : AdelicSpan φ :=
  mk φ (AdelicFnCarrier.mk φ) (mk_mem_adelicSpanSubmodule φ)

@[simp] theorem toFn_self : toFn φ (self φ) = AdelicFnCarrier.mk φ := rfl

theorem self_ne_zero_of_ne_zero (hφ : φ ≠ 0) : self φ ≠ 0 := by
  intro h
  exact AdelicFnCarrier.mk_ne_zero_of_ne_zero hφ (congrArg (toFn φ) h)

end AdelicSpan

variable (F)

theorem adelicSpan_self_one_ne_zero :
    AdelicSpan.self (F := F) (fun _ => (1 : ℂ)) ≠ 0 :=
  AdelicSpan.self_ne_zero_of_ne_zero _ (by intro h; exact one_ne_zero (congrFun h 1))

section PadicAction

variable (p : ℕ) [Fact p.Prime]

instance : DistribMulAction (GL (Fin 2) ℚ_[p]) (AdelicFnCarrier ℚ) :=
  DistribMulAction.compHom _ (AdelicDock.padicToAdelic p)

theorem AdelicFnCarrier.padic_smul_def (g : GL (Fin 2) ℚ_[p]) (φ : AdelicFnCarrier ℚ) :
    g • φ = (AdelicDock.padicToAdelic p g : AdelicGL2 (𝓞 ℚ) ℚ) • φ := rfl

instance : SMulCommClass ℂ (GL (Fin 2) ℚ_[p]) (AdelicFnCarrier ℚ) where
  smul_comm c g φ := smul_comm (α := AdelicFnCarrier ℚ) c (AdelicDock.padicToAdelic p g) φ

instance : SMulCommClass (GL (Fin 2) ℚ_[p]) ℂ (AdelicFnCarrier ℚ) :=
  SMulCommClass.symm _ _ _

variable {φ : AdelicGL2 (𝓞 ℚ) ℚ → ℂ}

instance : DistribMulAction (GL (Fin 2) ℚ_[p]) (AdelicSpan φ) :=
  DistribMulAction.compHom _ (AdelicDock.padicToAdelic p)

theorem AdelicSpan.padic_smul_def (g : GL (Fin 2) ℚ_[p]) (ψ : AdelicSpan φ) :
    g • ψ = (AdelicDock.padicToAdelic p g : AdelicGL2 (𝓞 ℚ) ℚ) • ψ := rfl

instance : SMulCommClass ℂ (GL (Fin 2) ℚ_[p]) (AdelicSpan φ) where
  smul_comm c g ψ := smul_comm (α := AdelicSpan φ) c (AdelicDock.padicToAdelic p g) ψ

instance : SMulCommClass (GL (Fin 2) ℚ_[p]) ℂ (AdelicSpan φ) :=
  SMulCommClass.symm _ _ _

theorem AdelicSpan.typeOf_hasNewvectorConductor (c : ℕ) :
    (HasNewvectorConductor p (AdelicSpan φ) c) = (HasNewvectorConductor p (AdelicSpan φ) c) := rfl

theorem AdelicSpan.typeOf_fixedSubmodule_padicK1 (n : ℕ) :
    (fixedSubmodule (padicK1 p n) (AdelicSpan φ) : Submodule ℂ (AdelicSpan φ))
      = fixedSubmodule (padicK1 p n) (AdelicSpan φ) := rfl

end PadicAction

end LocalNewvector

end



-- Prove2me | Definitions.Def_LieTwoAlg_Equiv_TwoVect
-- name    : LieTwoAlg_Equiv_TwoVect
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-22T02:23:46.393738+00:00
-- url     : https://prove2.me/theorems/58fdb5e7-2f23-40c4-8ecf-9eed305f45e2
-- title:
--   2-vector spaces, two-term complexes, and their linear maps
-- statement:
--   A $2$-vector space has vector spaces $V_0$ and $V_1$ and linear source, target, and identity maps $s,t:V_1\to V_0$ and $i:V_0\to V_1$ with $s(i(x))=t(i(x))=x$. For composable morphisms, composition is the formula forced by Lemma 6:
--
--   $$
--   fg=f+g-i(t(f)),\qquad \vec f=f-i(s(f))\in\ker s.
--   $$
--
--   The file also defines linear functors and natural transformations, two-term complexes $C_1\xrightarrow{d}C_0$, chain maps and chain homotopies. It gives the source's constructions $S(V)=(\ker s\xrightarrow{t}V_0)$ and $T(C)$ with arrows $C_0\oplus C_1$, together with their maps on morphisms.
--
--   These objects provide the linear category substrate for semistrict Lie $2$-algebras.
--
--   **Formalization Note** Composition is diagrammatic. Its category laws and uniqueness are the separate Lemma 6 milestone.
-- source:
--   Baez–Crans, Higher-Dimensional Algebra VI: Lie 2-Algebras, arXiv:math/0307263v6, pp. 9–15, Definition 5; Lemma 6; Definitions 7, 9, 11; Proposition 8

import Mathlib
import Definitions.Def_LieTwoAlg_Equiv_RawCat

set_option autoImplicit false

namespace LieTwoAlg.Equiv

universe u

/-- Definition 5, in the source/target/identity presentation of Lemma 6. -/
structure TwoVect (k : Type u) [Field k] where
  V0 : Type u
  V1 : Type u
  [add0 : AddCommGroup V0]
  [mod0 : Module k V0]
  [add1 : AddCommGroup V1]
  [mod1 : Module k V1]
  s : V1 →ₗ[k] V0
  t : V1 →ₗ[k] V0
  i : V0 →ₗ[k] V1
  s_i : ∀ x, s (i x) = x
  t_i : ∀ x, t (i x) = x
attribute [instance] TwoVect.add0 TwoVect.mod0 TwoVect.add1 TwoVect.mod1

variable {k : Type u} [Field k]

/-- Precompose both arguments of a curried bilinear map. -/
def preBilin {A B C D E : Type u}
    [AddCommGroup A] [Module k A] [AddCommGroup B] [Module k B]
    [AddCommGroup C] [Module k C] [AddCommGroup D] [Module k D]
    [AddCommGroup E] [Module k E]
    (b : B →ₗ[k] D →ₗ[k] E) (f : A →ₗ[k] B) (g : C →ₗ[k] D) :
    A →ₗ[k] C →ₗ[k] E where
  toFun a := (b (f a)).comp g
  map_add' a a' := by ext c; simp
  map_smul' c a := by ext d; simp

/-- Postcompose the value of a curried bilinear map. -/
def postBilin {A B C D : Type u}
    [AddCommGroup A] [Module k A] [AddCommGroup B] [Module k B]
    [AddCommGroup C] [Module k C] [AddCommGroup D] [Module k D]
    (h : C →ₗ[k] D) (b : A →ₗ[k] B →ₗ[k] C) : A →ₗ[k] B →ₗ[k] D where
  toFun a := h.comp (b a)
  map_add' a a' := by ext b'; simp
  map_smul' c a := by ext b'; simp

/-- Diagrammatic composition: first `f`, then `g`. -/
def TwoVect.comp (V : TwoVect k) (f g : V.V1) : V.V1 := f + g - V.i (V.t f)

def TwoVect.arrow (V : TwoVect k) (f : V.V1) : V.V1 := f - V.i (V.s f)

def TwoVect.arrowK (V : TwoVect k) : V.V1 →ₗ[k] LinearMap.ker V.s where
  toFun f := ⟨V.arrow f, by simp [TwoVect.arrow, V.s_i]⟩
  map_add' f g := by ext; simp [TwoVect.arrow, map_add]; abel
  map_smul' c f := by ext; simp [TwoVect.arrow, map_smul]; module

/-- The pullback of target and source for a composable pair. -/
def TwoVect.composable (V : TwoVect k) : Submodule k (V.V1 × V.V1) where
  carrier := {p | V.t p.1 = V.s p.2}
  zero_mem' := by simp
  add_mem' := by
    intro p q hp hq
    change V.t p.1 = V.s p.2 at hp
    change V.t q.1 = V.s q.2 at hq
    change V.t (p.1 + q.1) = V.s (p.2 + q.2)
    simp [hp, hq]
  smul_mem' := by
    intro c p hp
    change V.t p.1 = V.s p.2 at hp
    change V.t (c • p.1) = V.s (c • p.2)
    simp [hp]

def TwoVect.leftUnitPair (V : TwoVect k) (f : V.V1) : V.composable :=
  ⟨(V.i (V.s f), f), V.t_i _⟩

def TwoVect.rightUnitPair (V : TwoVect k) (f : V.V1) : V.composable :=
  ⟨(f, V.i (V.t f)), (V.s_i _).symm⟩

/-- Definitions 2 and 7: raw linear functor data. -/
structure LinFunctor (V W : TwoVect k) where
  F0 : V.V0 →ₗ[k] W.V0
  F1 : V.V1 →ₗ[k] W.V1

def IsLinFunctor {V W : TwoVect k} (F : LinFunctor V W) : Prop :=
  (∀ f, W.s (F.F1 f) = F.F0 (V.s f)) ∧
  (∀ f, W.t (F.F1 f) = F.F0 (V.t f)) ∧
  (∀ x, F.F1 (V.i x) = W.i (F.F0 x))

def LinFunctor.id (V : TwoVect k) : LinFunctor V V :=
  ⟨LinearMap.id, LinearMap.id⟩

def LinFunctor.comp {V W X : TwoVect k} (F : LinFunctor V W) (G : LinFunctor W X) :
    LinFunctor V X := ⟨G.F0.comp F.F0, G.F1.comp F.F1⟩

/-- Definition 9, componentwise naturality. -/
def IsLinNat {V W : TwoVect k} (F G : LinFunctor V W)
    (θ : V.V0 →ₗ[k] W.V1) : Prop :=
  (∀ x, W.s (θ x) = F.F0 x) ∧ (∀ x, W.t (θ x) = G.F0 x) ∧
  (∀ f, W.comp (F.F1 f) (θ (V.t f)) = W.comp (θ (V.s f)) (G.F1 f))

/-- Two-term chain complexes, §3. -/
structure TwoTerm (k : Type u) [Field k] where
  C0 : Type u
  C1 : Type u
  [add0 : AddCommGroup C0]
  [mod0 : Module k C0]
  [add1 : AddCommGroup C1]
  [mod1 : Module k C1]
  d : C1 →ₗ[k] C0
attribute [instance] TwoTerm.add0 TwoTerm.mod0 TwoTerm.add1 TwoTerm.mod1

structure ChainMap (C D : TwoTerm k) where
  φ0 : C.C0 →ₗ[k] D.C0
  φ1 : C.C1 →ₗ[k] D.C1

def IsChainMap {C D : TwoTerm k} (φ : ChainMap C D) : Prop :=
  ∀ h, D.d (φ.φ1 h) = φ.φ0 (C.d h)

def ChainMap.id (C : TwoTerm k) : ChainMap C C := ⟨LinearMap.id, LinearMap.id⟩
def ChainMap.comp {C D E : TwoTerm k} (φ : ChainMap C D) (ψ : ChainMap D E) :
    ChainMap C E := ⟨ψ.φ0.comp φ.φ0, ψ.φ1.comp φ.φ1⟩

/-- Chain homotopy from `φ` to `ψ`, §3 p. 14. -/
def IsChainHtpy {C D : TwoTerm k} (φ ψ : ChainMap C D)
    (τ : C.C0 →ₗ[k] D.C1) : Prop :=
  (∀ x, D.d (τ x) = ψ.φ0 x - φ.φ0 x) ∧
  (∀ h, τ (C.d h) = ψ.φ1 h - φ.φ1 h)

end LieTwoAlg.Equiv



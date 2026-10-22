-- Prove2me | Definitions.Def_LoopTwoGroup_Equiv_Model
-- name    : LoopTwoGroup_Equiv_Model
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-22T02:23:10.290391+00:00
-- url     : https://prove2.me/theorems/a3a4e25e-05ac-4214-8b3e-d6f3239dd1f8
-- title:
--   §§2–5 — 2-term L∞-algebras, smooth based paths and loops, P_k𝔤, 𝔤_k, and EΩ𝔤
-- statement:
--   The model uses a finite-dimensional real simple Lie algebra $\mathfrak g$ with an invariant positive-definite inner product $\langle\cdot,\cdot\rangle$. A based path is a smooth map $p:[0,2\pi]\to\mathfrak g$ with $p(0)=0$; a based loop also has $p(2\pi)=0$. Paths are represented by functions on $\mathbb R$ extended constantly outside the interval, so two representatives that agree on $[0,2\pi]$ are equal.
--
--   A **2-term $L_\infty$ datum** consists of vector spaces $V_0,V_1$, a linear differential $d:V_1\to V_0$, brackets $l_2$ in degrees $(0,0)$ and $(0,1)$, and a ternary bracket $l_3:V_0^3\to V_1$. Its homomorphisms are linear in degrees zero and one, carry a skew bilinear degree-two component, and satisfy the chain-map equation and equations (3)–(5) of Definition 2.7. A 2-homomorphism satisfies the two chain-homotopy equations and equation (7) of Definition 2.8. Composition uses equation (6).
--
--   The skeletal algebra $\mathfrak g_k$ has $V_0=\mathfrak g$, $V_1=\mathbb R$, $d=0$, trivial action on $V_1$, and
--   $$l_3(x,y,z)=k\langle x,[y,z]\rangle.$$
--   The path algebra $\mathcal P_k\mathfrak g$ has $V_0=P_0\mathfrak g$, $V_1=\Omega\mathfrak g\oplus\mathbb R$, differential $(\ell,c)\mapsto\ell$, pointwise bracket on paths, $l_3=0$, and
--   $$l_2(p,(\ell,c))=\left([p,\ell],\;2k\int_0^{2\pi}\langle\ell(\theta),p'(\theta)\rangle\,d\theta\right).$$
--   The algebra $E\Omega\mathfrak g$ has the same loop space in both degrees, identity differential, the loop bracket in both $l_2$ slots, and $l_3=0$.
--
--   These definitions provide the common objects for Theorem 5.1 and its component lemmas. **Formalization Note** The paper obtains $\mathcal P_k\mathfrak g$ from a Fréchet Lie 2-group; here its Proposition 4.2 formulas define it directly. Lie 2-algebras are read through the 2-term $L_\infty$ equivalence of Theorem 2.10. The HDA6 coherence laws are not stored in the datum. The basic-form normalization is dropped, while the invariant inner product and simplicity are retained; $k$ is real, as in §5. Derivatives are one-sided at the endpoints.
-- source:
--   Baez–Crans–Stevenson–Schreiber, From Loop Groups to 2-Groups, arXiv:math/0504123v3, pp. 9–12, 14–15, 19–20, 26–31; Definitions 2.7–2.8, equation (6), Example 2.15, Proposition 4.2, Lemma 5.2, and component formulas of Lemmas 5.4–5.7

import Mathlib

noncomputable section

namespace LoopTwoGroup.Equiv

open MeasureTheory InnerProductSpace

universe u v w x

/-- The data of a two-term L-infinity algebra used in Section 5. The coherence laws
are not part of this record; the paper invokes them from HDA6. -/
structure TwoTermData (V₀ : Type u) (V₁ : Type v)
    [AddCommGroup V₀] [Module ℝ V₀] [AddCommGroup V₁] [Module ℝ V₁] where
  d : V₁ →ₗ[ℝ] V₀
  l2 : V₀ → V₀ → V₀
  l2h : V₀ → V₁ → V₁
  l3 : V₀ → V₀ → V₀ → V₁

/-- Definition 2.7, including equations (3), (4), (5). -/
structure LInfHom {V₀ : Type u} {V₁ : Type v} {W₀ : Type w} {W₁ : Type x}
    [AddCommGroup V₀] [Module ℝ V₀] [AddCommGroup V₁] [Module ℝ V₁]
    [AddCommGroup W₀] [Module ℝ W₀] [AddCommGroup W₁] [Module ℝ W₁]
    (A : TwoTermData V₀ V₁) (B : TwoTermData W₀ W₁) where
  f0 : V₀ →ₗ[ℝ] W₀
  f1 : V₁ →ₗ[ℝ] W₁
  f2 : V₀ → V₀ → W₁
  f2_add : ∀ a b y, f2 (a + b) y = f2 a y + f2 b y
  f2_smul : ∀ (r : ℝ) a y, f2 (r • a) y = r • f2 a y
  f2_skew : ∀ a b, f2 a b = -f2 b a
  chain : ∀ h, B.d (f1 h) = f0 (A.d h)
  eq3 : ∀ a b, B.d (f2 a b) = f0 (A.l2 a b) - B.l2 (f0 a) (f0 b)
  eq4 : ∀ a h, f2 a (A.d h) = f1 (A.l2h a h) - B.l2h (f0 a) (f1 h)
  eq5 : ∀ a b c, f1 (A.l3 a b c) - B.l3 (f0 a) (f0 b) (f0 c) =
    f2 a (A.l2 b c) + f2 b (A.l2 c a) + f2 c (A.l2 a b) +
    B.l2h (f0 a) (f2 b c) + B.l2h (f0 b) (f2 c a) + B.l2h (f0 c) (f2 a b)

/-- Definition 2.8, equation (7), on raw components. -/
structure TwoHom {V₀ : Type u} {V₁ : Type v} {W₀ : Type w} {W₁ : Type x}
    [AddCommGroup V₀] [Module ℝ V₀] [AddCommGroup V₁] [Module ℝ V₁]
    [AddCommGroup W₀] [Module ℝ W₀] [AddCommGroup W₁] [Module ℝ W₁]
    (A : TwoTermData V₀ V₁) (B : TwoTermData W₀ W₁)
    (φ0 ψ0 : V₀ →ₗ[ℝ] W₀) (φ1 ψ1 : V₁ →ₗ[ℝ] W₁)
    (φ2 ψ2 : V₀ → V₀ → W₁) where
  τ : V₀ →ₗ[ℝ] W₁
  hom0 : ∀ a, B.d (τ a) = ψ0 a - φ0 a
  hom1 : ∀ h, τ (A.d h) = ψ1 h - φ1 h
  eq7 : ∀ a b, φ2 a b - ψ2 a b =
    B.l2h (φ0 a) (τ b) - B.l2h (ψ0 b) (τ a) - τ (A.l2 a b)

/-- Equation (6), the degree-zero part of a composite. -/
def compF0 {V₀ : Type u} {V₁ : Type v} {W₀ : Type w} {W₁ : Type x}
    {Z₀ Z₁ : Type*} [AddCommGroup V₀] [Module ℝ V₀] [AddCommGroup V₁] [Module ℝ V₁]
    [AddCommGroup W₀] [Module ℝ W₀] [AddCommGroup W₁] [Module ℝ W₁]
    [AddCommGroup Z₀] [Module ℝ Z₀] [AddCommGroup Z₁] [Module ℝ Z₁]
    {A : TwoTermData V₀ V₁} {B : TwoTermData W₀ W₁} {C : TwoTermData Z₀ Z₁}
    (F : LInfHom A B) (G : LInfHom B C) : V₀ →ₗ[ℝ] Z₀ := G.f0.comp F.f0

/-- Equation (6), the degree-one part of a composite. -/
def compF1 {V₀ : Type u} {V₁ : Type v} {W₀ : Type w} {W₁ : Type x}
    {Z₀ Z₁ : Type*} [AddCommGroup V₀] [Module ℝ V₀] [AddCommGroup V₁] [Module ℝ V₁]
    [AddCommGroup W₀] [Module ℝ W₀] [AddCommGroup W₁] [Module ℝ W₁]
    [AddCommGroup Z₀] [Module ℝ Z₀] [AddCommGroup Z₁] [Module ℝ Z₁]
    {A : TwoTermData V₀ V₁} {B : TwoTermData W₀ W₁} {C : TwoTermData Z₀ Z₁}
    (F : LInfHom A B) (G : LInfHom B C) : V₁ →ₗ[ℝ] Z₁ := G.f1.comp F.f1

/-- Equation (6), the bilinear part of a composite. -/
def compF2 {V₀ : Type u} {V₁ : Type v} {W₀ : Type w} {W₁ : Type x}
    {Z₀ Z₁ : Type*} [AddCommGroup V₀] [Module ℝ V₀] [AddCommGroup V₁] [Module ℝ V₁]
    [AddCommGroup W₀] [Module ℝ W₀] [AddCommGroup W₁] [Module ℝ W₁]
    [AddCommGroup Z₀] [Module ℝ Z₀] [AddCommGroup Z₁] [Module ℝ Z₁]
    {A : TwoTermData V₀ V₁} {B : TwoTermData W₀ W₁} {C : TwoTermData Z₀ Z₁}
    (F : LInfHom A B) (G : LInfHom B C) (a b : V₀) : Z₁ :=
  G.f2 (F.f0 a) (F.f0 b) + G.f1 (F.f2 a b)

/-- Equivalence through homomorphisms and 2-homomorphisms to each identity. -/
def Equivalent {V₀ : Type u} {V₁ : Type v} {W₀ : Type w} {W₁ : Type x}
    [AddCommGroup V₀] [Module ℝ V₀] [AddCommGroup V₁] [Module ℝ V₁]
    [AddCommGroup W₀] [Module ℝ W₀] [AddCommGroup W₁] [Module ℝ W₁]
    (A : TwoTermData V₀ V₁) (B : TwoTermData W₀ W₁) : Prop :=
  ∃ (F : LInfHom A B) (G : LInfHom B A),
    Nonempty (TwoHom A A (compF0 F G) LinearMap.id (compF1 F G) LinearMap.id
      (compF2 F G) (fun _ _ => 0)) ∧
    Nonempty (TwoHom B B (compF0 G F) LinearMap.id (compF1 G F) LinearMap.id
      (compF2 G F) (fun _ _ => 0))

/-- A specified homomorphism is an equivalence. -/
def IsEquivalence {V₀ : Type u} {V₁ : Type v} {W₀ : Type w} {W₁ : Type x}
    [AddCommGroup V₀] [Module ℝ V₀] [AddCommGroup V₁] [Module ℝ V₁]
    [AddCommGroup W₀] [Module ℝ W₀] [AddCommGroup W₁] [Module ℝ W₁]
    {A : TwoTermData V₀ V₁} {B : TwoTermData W₀ W₁} (F : LInfHom A B) : Prop :=
  ∃ G : LInfHom B A,
    Nonempty (TwoHom A A (compF0 F G) LinearMap.id (compF1 F G) LinearMap.id
      (compF2 F G) (fun _ _ => 0)) ∧
    Nonempty (TwoHom B B (compF0 G F) LinearMap.id (compF1 G F) LinearMap.id
      (compF2 G F) (fun _ _ => 0))

/-- The zero Lie 2-algebra. -/
def trivialData : TwoTermData (Fin 0 → ℝ) (Fin 0 → ℝ) where
  d := 0
  l2 := fun _ _ => 0
  l2h := fun _ _ => 0
  l3 := fun _ _ _ => 0

/-- The construction EL of Lemma 5.2. -/
def E {V : Type*} [AddCommGroup V] [Module ℝ V] (br : V → V → V) : TwoTermData V V where
  d := LinearMap.id
  l2 := br
  l2h := br
  l3 := fun _ _ _ => 0

/-- A real Lie bracket with the algebraic laws needed in Lemma 5.3. -/
structure RealLieBracket (V : Type*) [AddCommGroup V] [Module ℝ V] where
  br : V →ₗ[ℝ] V →ₗ[ℝ] V
  self : ∀ a, br a a = 0
  jacobi : ∀ a b c, br a (br b c) + br b (br c a) + br c (br a b) = 0

/-- A finite-dimensional compact simple real Lie algebra with invariant inner product. -/
structure InvLieBracket (g : Type*) [NormedAddCommGroup g] [InnerProductSpace ℝ g] where
  br : g →L[ℝ] g →L[ℝ] g
  self : ∀ a, br a a = 0
  jacobi : ∀ a b c, br a (br b c) + br b (br c a) + br c (br a b) = 0
  invariant : ∀ a b c, ⟪br a b, c⟫_ℝ = ⟪a, br b c⟫_ℝ
  simple : (∃ a b, br a b ≠ 0) ∧
    ∀ I : Submodule ℝ g, (∀ a, ∀ b ∈ I, br a b ∈ I) → I = ⊥ ∨ I = ⊤

/-- A fixed representative of a smooth function on the closed path interval. -/
def clamp (t : ℝ) : ℝ := max 0 (min t (2 * Real.pi))

/-- The smooth based paths, extended constantly off the defining interval. -/
def pathSpace (g : Type*) [NormedAddCommGroup g] [NormedSpace ℝ g] :
    Submodule ℝ (ℝ → g) where
  carrier := {p | ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) p (Set.Icc 0 (2 * Real.pi)) ∧
    p 0 = 0 ∧ ∀ t, p t = p (clamp t)}
  zero_mem' := by
    refine ⟨?_, rfl, ?_⟩
    · exact contDiffOn_const
    · intro t; rfl
  add_mem' := by
    intro p q hp hq
    refine ⟨hp.1.add hq.1, ?_, ?_⟩
    · simp [hp.2.1, hq.2.1]
    · intro t; simp only [Pi.add_apply, hp.2.2 t, hq.2.2 t]
  smul_mem' := by
    intro r p hp
    refine ⟨hp.1.const_smul r, ?_, ?_⟩
    · simp [hp.2.1]
    · intro t; simp only [Pi.smul_apply, hp.2.2 t]

/-- Smooth loops based at both endpoints. -/
def loopSpace (g : Type*) [NormedAddCommGroup g] [NormedSpace ℝ g] :
    Submodule ℝ (ℝ → g) where
  carrier := {p | p ∈ pathSpace g ∧ p (2 * Real.pi) = 0}
  zero_mem' := by simp
  add_mem' := by
    intro p q hp hq
    refine ⟨(pathSpace g).add_mem hp.1 hq.1, ?_⟩
    simp [hp.2, hq.2]
  smul_mem' := by
    intro r p hp
    refine ⟨(pathSpace g).smul_mem r hp.1, ?_⟩
    simp [hp.2]

/-- The derivative on the closed path interval; at endpoints it is one-sided. -/
def dpath {g : Type*} [NormedAddCommGroup g] [NormedSpace ℝ g] (p : ℝ → g) : ℝ → g :=
  derivWithin p (Set.Icc 0 (2 * Real.pi))

variable {g : Type*} [NormedAddCommGroup g] [InnerProductSpace ℝ g]

/-- Pointwise bracket on paths. -/
def pathBracket (L : InvLieBracket g) (p q : pathSpace g) : pathSpace g := by
  refine ⟨fun t => L.br (p.1 t) (q.1 t), ?_⟩
  refine ⟨?_, ?_, ?_⟩
  · exact (p.2.1.continuousLinearMap_comp L.br).clm_apply q.2.1
  · simp [p.2.2.1, q.2.2.1]
  · intro t
    change L.br (p.1 t) (q.1 t) = L.br (p.1 (clamp t)) (q.1 (clamp t))
    rw [p.2.2.2 t, q.2.2.2 t]

/-- Pointwise bracket on loops. -/
def loopBracket (L : InvLieBracket g) (p q : loopSpace g) : loopSpace g := by
  refine ⟨(pathBracket L ⟨p.1, p.2.1⟩ ⟨q.1, q.2.1⟩).1, ?_⟩
  refine ⟨(pathBracket L ⟨p.1, p.2.1⟩ ⟨q.1, q.2.1⟩).2, ?_⟩
  simp [pathBracket, p.2.2, q.2.2]

/-- Pointwise bracket of a path and a loop. -/
def pathLoopBracket (L : InvLieBracket g) (p : pathSpace g) (q : loopSpace g) :
    loopSpace g := by
  refine ⟨(pathBracket L p ⟨q.1, q.2.1⟩).1, ?_⟩
  refine ⟨(pathBracket L p ⟨q.1, q.2.1⟩).2, ?_⟩
  simp [pathBracket, q.2.2]

/-- Lemma 5.2 specialized to the based loop algebra. -/
def EOmega (L : InvLieBracket g) : TwoTermData (loopSpace g) (loopSpace g) :=
  E (loopBracket L)

/-- Example 2.15: the skeletal string Lie 2-algebra. -/
def gk (L : InvLieBracket g) (k : ℝ) : TwoTermData g ℝ where
  d := 0
  l2 := fun a b => L.br a b
  l2h := fun _ _ => 0
  l3 := fun a b c => k * ⟪a, L.br b c⟫_ℝ

/-- Proposition 4.2: the path Lie 2-algebra, in its two-term L-infinity description. -/
def Pk (L : InvLieBracket g) (k : ℝ) :
    TwoTermData (pathSpace g) (loopSpace g × ℝ) where
  d :=
    { toFun := fun h => ⟨h.1.1, h.1.2.1⟩
      map_add' := by intro a b; ext t; rfl
      map_smul' := by intro r a; ext t; rfl }
  l2 := pathBracket L
  l2h := fun p h =>
    (pathLoopBracket L p h.1,
      2 * k * ∫ θ in (0 : ℝ)..(2 * Real.pi), ⟪h.1.1 θ, dpath p.1 θ⟫_ℝ)
  l3 := fun _ _ _ => 0

/-- The three displayed component formulas of Lemma 5.4. -/
def PhiComponents (L : InvLieBracket g) (k : ℝ)
    (Φ : LInfHom (Pk L k) (gk L k)) : Prop :=
  (∀ p, Φ.f0 p = p.1 (2 * Real.pi)) ∧
  (∀ h, Φ.f1 h = h.2) ∧
  (∀ p q, Φ.f2 p q =
    k * ∫ θ in (0 : ℝ)..(2 * Real.pi),
      (⟪q.1 θ, dpath p.1 θ⟫_ℝ - ⟪dpath q.1 θ, p.1 θ⟫_ℝ))

/-- The three displayed component formulas in the proof of Lemma 5.5. -/
def LambdaComponents (L : InvLieBracket g) (k : ℝ)
    (Λ : LInfHom (EOmega L) (Pk L k)) : Prop :=
  (∀ ℓ, Λ.f0 ℓ = (⟨ℓ.1, ℓ.2.1⟩ : pathSpace g)) ∧
  (∀ ℓ, Λ.f1 ℓ = (ℓ, 0)) ∧
  (∀ ℓ₁ ℓ₂, Λ.f2 ℓ₁ ℓ₂ =
    (0, 2 * k * ∫ θ in (0 : ℝ)..(2 * Real.pi),
      ⟪ℓ₁.1 θ, dpath ℓ₂.1 θ⟫_ℝ))

/-- The displayed components of Lemma 5.7, with the interval function clamped
outside its domain. -/
def PsiComponents (L : InvLieBracket g) (k : ℝ) (f : ℝ → ℝ)
    (Ψ : LInfHom (gk L k) (Pk L k)) : Prop :=
  (∀ a t, (Ψ.f0 a).1 t = f (clamp t) • a) ∧
  (∀ c, Ψ.f1 c = ((0 : loopSpace g), c)) ∧
  (∀ a b t, ((Ψ.f2 a b).1).1 t = (f (clamp t) - f (clamp t) ^ 2) • L.br a b) ∧
  (∀ a b, (Ψ.f2 a b).2 = 0)

end LoopTwoGroup.Equiv



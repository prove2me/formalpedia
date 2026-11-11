-- Prove2me | Definitions.Def_SubspaceEvasion312_Explicit_algebra
-- name    : SubspaceEvasion312_Explicit_algebra
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-11T03:57:58.089896+00:00
-- url     : https://prove2.me/theorems/9e9f72d4-671d-4153-b92d-3fdaad76b6f8
-- title:
--   Vector spaces, additive codes, evasion and subspace list recovery
-- statement:
--   Let $F$ be a field, $V_n=F^{\{0,\ldots,n-1\}}$, and $W_{s,m}=(V_s)^m$. An additive code is an $F$-linear subspace $C\le W_{s,m}$, with rate $\dim_F C/(sm)$ when $s,m>0$. An encoder $E:V_k\to W_{s,m}$ is linear, has image $C$, and has $k=\dim_F C$.
--
--   A set $A$ is linearly $(r,c)$ evasive when every linear subspace $U$ of dimension at most $r$ has finite intersection with $A$, of cardinality at most $c$. Affine evasion uses every translate $a+U$ instead. The graph of $f:X\to Y$ is $G^f=\{(x,f(x)):x\in X\}$, with its canonical bijection from $X$.
--
--   For lists $S_i\subseteq V_s$ of size at most $\ell$, subspace list recovery bounds the number of $c\in C\cap U$ admitting $y\in\prod_i S_i$ with block Hamming distance at most $\rho m$. A finite-subset formulation represents real or infinite output bounds faithfully, without treating an infinite recovered set as having cardinality zero.
--
--   A lossless rank condenser has a coordinate projection injective on every subspace of $C$ of dimension at most $r$. A design parameter is any $\tau:\mathbb N\to\mathbb R$ bounded above by one; it need not be nonnegative. Writing $A_i=\{a\in A:a_i=0\}$, its design condition is
--
--   $$\frac1m\sum_i\dim_F A_i\le\dim_F A\,\tau(t)\qquad(A\le C,\ \dim_F A\le t).$$
--
--   The zero code is allowed. The zero-error power bound is zero for empty input lists at positive length, the exact real power for $\tau(r)<1$, and $+\infty$ at $\tau(r)=1$ with nonempty lists. Logarithms used quantitatively are base two. The actual composed function is $g(x)_i=f(E(x)_i)$; its graph retains the message prefix. These shared definitions support all ten source results.
-- source:
--   Brakensiek, Chen, Cheraghchi, Goyal, Guruswami, Putterman, Zhang, STOC 2027 submission #312 (October 2026), Definitions 3, 4, 7, 11, 13; encoder and complexity conventions, printed p. 2 (PDF p. 3); https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/312.pdf; PDF SHA256 a6946cb436bf453cfc53c1547fdd79e55134761b2192ee39f145dfc45490f6bc; also printed pp. 7, 9–10 (PDF pp. 8, 10–11)

import Mathlib

noncomputable section

namespace SubspaceEvasion312.Explicit
open scoped BigOperators ENNReal

abbrev Vec (F : Type) (n : ℕ) := Fin n → F
abbrev Blocks (F : Type) (s m : ℕ) := Fin m → Vec F s
abbrev Code (F : Type) [Field F] (s m : ℕ) := Submodule F (Blocks F s m)

/-- Definition 3. Finiteness is explicit even over an infinite field. -/
def Evasive {F V : Type} [Field F] [AddCommGroup V] [Module F V]
    [FiniteDimensional F V] (A : Set V) (r c : ℕ) : Prop :=
  ∀ U : Submodule F V, Module.finrank F U ≤ r →
    (A ∩ (U : Set V)).Finite ∧ (A ∩ (U : Set V)).ncard ≤ c

/-- The introductory convention: translates of linear spaces. -/
def AffineEvasive {F : Type} [Field F] {n : ℕ} (A : Set (Vec F n)) (r c : ℕ) : Prop :=
  ∀ U : Submodule F (Vec F n), Module.finrank F U ≤ r → ∀ a : Vec F n,
    (A ∩ {x | x - a ∈ U}).Finite ∧ (A ∩ {x | x - a ∈ U}).ncard ≤ c

/-- Definition 7, with the two coordinate blocks kept visible. -/
def graph {X Y : Type} (f : X → Y) : Set (X × Y) := {z | z.2 = f z.1}

def graphEquiv {X Y : Type} (f : X → Y) : X ≃ graph f where
  toFun x := ⟨(x, f x), rfl⟩
  invFun z := z.val.1
  left_inv _ := rfl
  right_inv z := by
    apply Subtype.ext
    have h : z.val.2 = f z.val.1 := z.property
    exact Prod.ext rfl h.symm

def hamming {F : Type} {s m : ℕ} (x y : Blocks F s m) : ℕ := by
  classical exact (Finset.univ.filter (fun i => x i ≠ y i)).card

/-- Definition 4, including the existential witness in the product of input lists. -/
def recovered {F : Type} [Field F] {s m : ℕ} (C : Code F s m)
    (U : Submodule F (Blocks F s m)) (S : Fin m → Finset (Vec F s))
    (ρ : ℝ) : Set (Blocks F s m) :=
  {c | c ∈ C ∧ c ∈ U ∧ ∃ y : Blocks F s m,
    (∀ i, y i ∈ S i) ∧ (hamming c y : ℝ) ≤ ρ * m}

/-- Finite output bounds cannot hold vacuously for infinite recovered sets.
The extended value top is used only for the endpoint in Corollary 16. -/
def ListRecoverable {F : Type} [Field F] {s m : ℕ} (C : Code F s m)
    (r : ℕ) (ρ : ℝ) (ℓ : ℕ) (L : ℝ≥0∞) : Prop :=
  ∀ U : Submodule F (Blocks F s m), Module.finrank F U ≤ r →
    ∀ S : Fin m → Finset (Vec F s), (∀ i, (S i).card ≤ ℓ) →
      ∀ T : Finset (Blocks F s m), (↑T : Set _) ⊆ recovered C U S ρ →
        (T.card : ℝ≥0∞) ≤ L

/-- Dimension-correct source encoder; injectivity is not an independent assumption. -/
def IsEncoder {F : Type} [Field F] {s m k : ℕ}
    (C : Code F s m) (E : Vec F k →ₗ[F] Blocks F s m) : Prop :=
  k = Module.finrank F C ∧ LinearMap.range E = C

def codeRate {F : Type} [Field F] {s m : ℕ} (C : Code F s m) : ℝ :=
  (Module.finrank F C : ℝ) / (s * m : ℕ)

/-- Definition 11, including the zero subspace. -/
def RankCondenser {F : Type} [Field F] {s m : ℕ} (C : Code F s m) (r : ℕ) : Prop :=
  ∀ U : Submodule F (Blocks F s m), U ≤ C → Module.finrank F U ≤ r →
    ∃ i : Fin m, Set.InjOn (fun x : Blocks F s m => x i) U

def coordinateKernel {F : Type} [Field F] {s m : ℕ}
    (A : Submodule F (Blocks F s m)) (i : Fin m) : Submodule F (Blocks F s m) where
  carrier := {a | a ∈ A ∧ a i = 0}
  zero_mem' := by simp
  add_mem' := by intro a b ha hb; exact ⟨A.add_mem ha.1 hb.1, by simp [ha.2, hb.2]⟩
  smul_mem' := by intro a x hx; exact ⟨A.smul_mem a hx.1, by simp [hx.2]⟩

/-- Definition 13: tau is bounded above by one, with no lower bound. -/
def SubspaceDesign {F : Type} [Field F] {s m : ℕ}
    (C : Code F s m) (τ : ℕ → ℝ) : Prop :=
  (∀ t, τ t ≤ 1) ∧ ∀ t (A : Submodule F (Blocks F s m)),
    A ≤ C → Module.finrank F A ≤ t →
      (∑ i : Fin m, (Module.finrank F (coordinateKernel A i) : ℝ)) / m ≤
        (Module.finrank F A : ℝ) * τ t

def log₂ (x : ℝ) : ℝ := Real.log x / Real.log 2

def zeroErrorBound (ℓ : ℕ) (τr : ℝ) : ℝ≥0∞ :=
  if ℓ = 0 then 0 else if τr < 1 then ENNReal.ofReal ((ℓ : ℝ) ^ (1 / (1 - τr))) else ⊤

/-- Theorem 8's actual composition. -/
def compose {F : Type} [Field F] {s b m k : ℕ}
    (E : Vec F k →ₗ[F] Blocks F s m) (f : Vec F s → Vec F b)
    (x : Vec F k) : Blocks F b m := fun i => f (E x i)

end SubspaceEvasion312.Explicit



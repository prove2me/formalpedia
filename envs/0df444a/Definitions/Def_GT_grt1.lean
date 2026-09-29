-- Prove2me | Definitions.Def_GT_grt1
-- name    : GT_grt1
-- status  : Definition
-- author  : @Lucas
-- created : 2026-09-13T20:52:33.280665+00:00
-- url     : https://prove2.me/theorems/c674dbb8-5ac8-41ac-a5a9-7cc4a5d51a9d
-- title:
--   The Lie algebra $\mathfrak{grt}_1$ and the Ihara bracket
-- statement:
--   This file sets up the **graded Grothendieck-Teichmüller Lie algebra** $\mathfrak{grt}_1$ and the **Ihara (Poisson) bracket** on the free Lie algebra in two variables.
--
--   Let $\mathbb F(x,y)$ be the free Lie algebra over $\mathbb Q$ on generators $x$ and $y$. For a Lie $\mathbb Q$-algebra $A$ and $a,b \in A$, substitution $\psi \mapsto \psi(a,b)$ is the unique Lie algebra morphism $\mathbb F(x,y) \to A$ with $x \mapsto a$, $y \mapsto b$.
--
--   $\mathfrak{grt}_1$ is the set of $\psi \in \mathbb F(x,y)$ satisfying the three defining equations of the source:
--
--   $$\psi(y,x) = -\psi(x,y) \tag{4.7}$$
--
--   $$\psi(x,y) + \psi(y,z) + \psi(z,x) = 0, \qquad z = -x-y \tag{4.8}$$
--
--   $$\psi(t_{12},t_{23}) - \psi(t_{12},t_{23}+t_{24}) + \psi(t_{12}+t_{13},t_{24}+t_{34}) - \psi(t_{13}+t_{23},t_{34}) + \psi(t_{23},t_{34}) = 0 \tag{4.9}$$
--
--   the last equation taking place in the Drinfeld-Kohno Lie algebra $\mathfrak t_4$. All three are linear in $\psi$, so $\mathfrak{grt}_1$ is a $\mathbb Q$-subspace; it is defined here as the intersection of the kernels of the three corresponding linear maps.
--
--   An element $\psi$ is called homogeneous of degree $n$ when $\psi(cx,cy) = c^n\,\psi(x,y)$ for every rational $c$; over $\mathbb Q$ this is equivalent to homogeneity for the word-length grading.
--
--   For $f \in \mathbb F(x,y)$, the **Ihara derivation** $D_f$ is the derivation with $D_f x = 0$ and $D_f y = [y,f]$; it is constructed here through the semidirect product $\mathbb F(x,y) \ltimes \mathbb F(x,y)$ of the free Lie algebra with its adjoint module. The **Ihara bracket** is
--
--   $$\{f,g\} = [f,g] + D_f g - D_g f .$$
--
--   $\mathfrak{grt}_1$ is not a Lie subalgebra for $[\,,\,]$, but it is one for $\{\,,\}$; that is the structure under which the Deligne-Drinfeld-Ihara conjecture speaks of freeness.
--
--   **Formalization Note.** Two deliberate deviations from the source text. First, $\mathfrak{grt}_1$ is modelled by Lie *polynomials* rather than by the completed free Lie algebra $\widehat{\mathbb F}(x,y)$; the three equations are homogeneous, so this is the graded avatar of the object in the notes. Second, the source writes $D_f x = x$ (Remark 4.4 and Section 7.3), which contradicts both Lemma 7.2 and the computation $\{x,y\} = [x,y]+[y,x] = 0$ of Remark 7.2; the convention $D_f x = 0$, used here, is the one under which those two assertions of the source are correct.
-- source:
--   Thomas Willwacher, The Grothendieck-Teichmüller Group, ETH Zürich lecture notes (in progress), 27 February 2014, Section 4.2, p. 45-46 (Drinfeld-Kohno Lie algebra t_n; Proposition 4.4, equations (4.7), (4.8), (4.9)); Thomas Willwacher, The Grothendieck-Teichmüller Group, ETH Zürich lecture notes (in progress), 27 February 2014, Section 7.3, p. 55 (Lemma 7.2, Corollary 7.1, Remarks 7.1 and 7.2); Remark 4.4, p. 47

import Definitions.Def_GT_DrinfeldKohno

/-!
# The graded Grothendieck-Teichmüller Lie algebra `grt₁` and the Ihara (Poisson) bracket

Willwacher, *The Grothendieck-Teichmüller Group* (ETH lecture notes, 27 Feb 2014):
Proposition 4.4, equations (4.7), (4.8), (4.9), p. 46; Remark 4.4, p. 47;
Section 7.3 (Lemma 7.2, Corollary 7.1), p. 55.
-/

namespace GrothendieckTeichmuller

open FreeLieAlgebra

noncomputable section

/-- The free Lie algebra on two generators `x`, `y` over `ℚ`. Elements of `grt₁` are the
Lie polynomials `ψ(x, y)` living here; this is the graded (polynomial) model of the
completed free Lie algebra `F̂Lie(x, y)` of the source. -/
abbrev Lxy : Type := FreeLieAlgebra ℚ (Fin 2)

/-- The first generator `x`. -/
def gx : Lxy := of ℚ 0

/-- The second generator `y`. -/
def gy : Lxy := of ℚ 1

/-- Substitution `ψ ↦ ψ(a, b)`: the unique Lie algebra morphism from the free Lie algebra on
`x`, `y` to a Lie `ℚ`-algebra `A` sending `x ↦ a` and `y ↦ b`. -/
def substXY {A : Type*} [LieRing A] [LieAlgebra ℚ A] (a b : A) : Lxy →ₗ⁅ℚ⁆ A :=
  lift ℚ (fun i : Fin 2 => if i = 0 then a else b)

@[simp] lemma substXY_gx {A : Type*} [LieRing A] [LieAlgebra ℚ A] (a b : A) :
    substXY a b gx = a := by
  simp [substXY, gx]

@[simp] lemma substXY_gy {A : Type*} [LieRing A] [LieAlgebra ℚ A] (a b : A) :
    substXY a b gy = b := by
  simp [substXY, gy]

/-! ### The defining equations of `grt₁` -/

/-- The antisymmetry operator `ψ ↦ ψ(y, x) + ψ(x, y)`; equation (4.7) says it vanishes. -/
def grtAntisymMap : Lxy →ₗ[ℚ] Lxy :=
  (substXY gy gx : Lxy →ₗ⁅ℚ⁆ Lxy).toLinearMap + LinearMap.id

/-- The hexagon operator `ψ ↦ ψ(x, y) + ψ(y, z) + ψ(z, x)` with `z = -x - y`;
equation (4.8) says it vanishes. -/
def grtHexagonMap : Lxy →ₗ[ℚ] Lxy :=
  (substXY gx gy : Lxy →ₗ⁅ℚ⁆ Lxy).toLinearMap +
    (substXY gy (-gx - gy) : Lxy →ₗ⁅ℚ⁆ Lxy).toLinearMap +
    (substXY (-gx - gy) gx : Lxy →ₗ⁅ℚ⁆ Lxy).toLinearMap

/-- The pentagon operator, with values in the Drinfeld-Kohno Lie algebra `t₄`:
`ψ ↦ ψ(t₁₂, t₂₃) - ψ(t₁₂, t₂₃ + t₂₄) + ψ(t₁₂ + t₁₃, t₂₄ + t₃₄) - ψ(t₁₃ + t₂₃, t₃₄) + ψ(t₂₃, t₃₄)`;
equation (4.9) says it vanishes. Indices `1, 2, 3, 4` are the elements `0, 1, 2, 3` of `Fin 4`. -/
def grtPentagonMap : Lxy →ₗ[ℚ] DrinfeldKohno 4 :=
  (substXY (dkGen 0 1) (dkGen 1 2) : Lxy →ₗ⁅ℚ⁆ DrinfeldKohno 4).toLinearMap -
    (substXY (dkGen 0 1) (dkGen 1 2 + dkGen 1 3) : Lxy →ₗ⁅ℚ⁆ DrinfeldKohno 4).toLinearMap +
    (substXY (dkGen 0 1 + dkGen 0 2) (dkGen 1 3 + dkGen 2 3) :
      Lxy →ₗ⁅ℚ⁆ DrinfeldKohno 4).toLinearMap -
    (substXY (dkGen 0 2 + dkGen 1 2) (dkGen 2 3) : Lxy →ₗ⁅ℚ⁆ DrinfeldKohno 4).toLinearMap +
    (substXY (dkGen 1 2) (dkGen 2 3) : Lxy →ₗ⁅ℚ⁆ DrinfeldKohno 4).toLinearMap

/-- The graded Grothendieck-Teichmüller Lie algebra `grt₁`, as a `ℚ`-subspace of the free Lie
algebra on `x`, `y`: the Lie polynomials `ψ` satisfying the antisymmetry equation (4.7), the
hexagon equation (4.8) and the pentagon equation (4.9). -/
def grt1 : Submodule ℚ Lxy :=
  LinearMap.ker grtAntisymMap ⊓ LinearMap.ker grtHexagonMap ⊓ LinearMap.ker grtPentagonMap

lemma mem_grt1_iff (ψ : Lxy) :
    ψ ∈ grt1 ↔
      substXY gy gx ψ = -ψ ∧
      substXY gx gy ψ + substXY gy (-gx - gy) ψ + substXY (-gx - gy) gx ψ = 0 ∧
      substXY (dkGen (0 : Fin 4) 1) (dkGen 1 2) ψ -
            substXY (dkGen (0 : Fin 4) 1) (dkGen 1 2 + dkGen 1 3) ψ +
          substXY (dkGen (0 : Fin 4) 1 + dkGen 0 2) (dkGen 1 3 + dkGen 2 3) ψ -
          substXY (dkGen (0 : Fin 4) 2 + dkGen 1 2) (dkGen 2 3) ψ +
          substXY (dkGen (1 : Fin 4) 2) (dkGen 2 3) ψ = 0 := by
  simp only [grt1, Submodule.mem_inf, LinearMap.mem_ker, grtAntisymMap, grtHexagonMap,
    grtPentagonMap, LinearMap.add_apply, LinearMap.sub_apply, LinearMap.id_apply,
    LieHom.coe_toLinearMap, add_eq_zero_iff_eq_neg, and_assoc]

/-- `ψ` is homogeneous of degree `n`: rescaling both generators by `c` rescales `ψ` by `cⁿ`.
Over `ℚ` this is exactly homogeneity of degree `n` for the grading by total word length. -/
def IsHomogeneousOfDegree (n : ℕ) (ψ : Lxy) : Prop :=
  ∀ c : ℚ, substXY (c • gx) (c • gy) ψ = c ^ n • ψ

/-! ### The Ihara (Poisson) bracket -/

/-- The semidirect product `F_Lie(x, y) ⋉ F_Lie(x, y)` of the free Lie algebra with its adjoint
module, used to construct the Ihara derivations. -/
def AdExt : Type := Lxy × Lxy

namespace AdExt

instance : AddCommGroup AdExt := inferInstanceAs (AddCommGroup (Lxy × Lxy))

instance : Module ℚ AdExt := inferInstanceAs (Module ℚ (Lxy × Lxy))

/-- The underlying pair of an element of the semidirect product. -/
def toPair (p : AdExt) : Lxy × Lxy := p

@[simp] lemma toPair_zero : toPair 0 = 0 := rfl

@[simp] lemma toPair_add (p q : AdExt) : toPair (p + q) = toPair p + toPair q := rfl

@[simp] lemma toPair_smul (c : ℚ) (p : AdExt) : toPair (c • p) = c • toPair p := rfl

instance : Bracket AdExt AdExt :=
  ⟨fun p q => (((⁅(toPair p).1, (toPair q).1⁆,
    ⁅(toPair p).1, (toPair q).2⁆ - ⁅(toPair q).1, (toPair p).2⁆) : Lxy × Lxy) : AdExt)⟩

@[simp] lemma toPair_bracket (p q : AdExt) :
    toPair ⁅p, q⁆ = ((⁅(toPair p).1, (toPair q).1⁆,
      ⁅(toPair p).1, (toPair q).2⁆ - ⁅(toPair q).1, (toPair p).2⁆) : Lxy × Lxy) := rfl

lemma ext' {p q : AdExt} (h1 : (toPair p).1 = (toPair q).1) (h2 : (toPair p).2 = (toPair q).2) :
    p = q := Prod.ext h1 h2

instance : LieRing AdExt where
  add_lie p q r := by
    refine ext' ?_ ?_ <;> (simp [add_lie, lie_add]; try abel)
  lie_add p q r := by
    refine ext' ?_ ?_ <;> (simp [add_lie, lie_add]; try abel)
  lie_self p := by
    refine ext' ?_ ?_ <;> simp
  leibniz_lie p q r := by
    refine ext' ?_ ?_
    · simp only [toPair_bracket, toPair_add, Prod.fst_add]
      exact leibniz_lie _ _ _
    · simp only [toPair_bracket, toPair_add, Prod.snd_add, lie_sub]
      rw [leibniz_lie (toPair p).1 (toPair q).1 (toPair r).2,
        leibniz_lie (toPair p).1 (toPair r).1 (toPair q).2,
        lie_lie (toPair q).1 (toPair r).1 (toPair p).2]
      abel

instance : LieAlgebra ℚ AdExt where
  lie_smul c p q := by
    refine ext' ?_ ?_ <;> simp [smul_sub]

/-- The projection `F_Lie(x, y) ⋉ F_Lie(x, y) → F_Lie(x, y)`, a morphism of Lie algebras. -/
def fstHom : AdExt →ₗ⁅ℚ⁆ Lxy where
  toFun p := (toPair p).1
  map_add' _ _ := rfl
  map_smul' _ _ := rfl
  map_lie' := rfl

@[simp] lemma fstHom_apply (p : AdExt) : fstHom p = (toPair p).1 := rfl

end AdExt

/-- The Lie algebra morphism `u ↦ (u, D_f u)` into the semidirect product, where `D_f` is the
Ihara derivation attached to `f`: the derivation with `D_f x = 0` and `D_f y = ⁅y, f⁆`. -/
def iharaHom (f : Lxy) : Lxy →ₗ⁅ℚ⁆ AdExt :=
  lift ℚ (fun i : Fin 2 =>
    if i = 0 then ((⟨gx, 0⟩ : Lxy × Lxy) : AdExt) else ((⟨gy, ⁅gy, f⁆⟩ : Lxy × Lxy) : AdExt))

lemma iharaHom_fst (f u : Lxy) : (AdExt.toPair (iharaHom f u)).1 = u := by
  have h : (AdExt.fstHom.comp (iharaHom f) : Lxy →ₗ⁅ℚ⁆ Lxy) = LieHom.id := by
    apply FreeLieAlgebra.hom_ext
    intro i
    fin_cases i <;> simp [iharaHom, AdExt.fstHom, AdExt.toPair, gx, gy]
  calc (AdExt.toPair (iharaHom f u)).1 = (AdExt.fstHom.comp (iharaHom f)) u := rfl
    _ = LieHom.id u := by rw [h]
    _ = u := rfl

/-- The Ihara derivation `D_f` of the free Lie algebra on `x`, `y`: the unique derivation with
`D_f x = 0` and `D_f y = ⁅y, f⁆`. -/
def iharaDeriv (f : Lxy) : LieDerivation ℚ Lxy Lxy where
  toFun u := (AdExt.toPair (iharaHom f u)).2
  map_add' u v := by
    have h := map_add (iharaHom f) u v
    exact congrArg (fun z : AdExt => (AdExt.toPair z).2) h
  map_smul' c u := by
    have h := map_smul (iharaHom f) c u
    exact congrArg (fun z : AdExt => (AdExt.toPair z).2) h
  leibniz' u v := by
    show (AdExt.toPair (iharaHom f ⁅u, v⁆)).2 =
      ⁅u, (AdExt.toPair (iharaHom f v)).2⁆ - ⁅v, (AdExt.toPair (iharaHom f u)).2⁆
    rw [(iharaHom f).map_lie u v]
    simp only [AdExt.toPair_bracket, iharaHom_fst]

@[simp] lemma iharaDeriv_apply (f u : Lxy) : iharaDeriv f u = (AdExt.toPair (iharaHom f u)).2 := rfl

@[simp] lemma iharaDeriv_gx (f : Lxy) : iharaDeriv f gx = 0 := by
  simp [iharaDeriv, iharaHom, gx, AdExt.toPair]

@[simp] lemma iharaDeriv_gy (f : Lxy) : iharaDeriv f gy = ⁅gy, f⁆ := by
  simp [iharaDeriv, iharaHom, gy, AdExt.toPair]

/-- The Ihara (Poisson) bracket on the free Lie algebra on `x`, `y`:
`{f, g} = ⁅f, g⁆ + D_f g - D_g f`. -/
def iharaBracket (f g : Lxy) : Lxy := ⁅f, g⁆ + iharaDeriv f g - iharaDeriv g f

end

end GrothendieckTeichmuller



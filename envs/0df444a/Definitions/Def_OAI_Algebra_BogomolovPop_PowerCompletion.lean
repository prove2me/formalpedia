-- Prove2me | Definitions.Def_OAI_Algebra_BogomolovPop_PowerCompletion
-- name    : OAI_Algebra_BogomolovPop_PowerCompletion
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-10-14T20:22:19.530507+00:00
-- url     : https://prove2.me/theorems/b56a616b-7cb2-422e-a66d-6486a339b68c
-- title:
--   Power classes, $\ell$-adic power completions, degree characters and Kummer scalar relations
-- statement:
--   This file provides the multiplicative bookkeeping used for Kummer theory: classes of group elements modulo $q$-th powers, their $\ell$-adic inverse limit, homomorphisms between unit groups of fields, integer-valued degree characters on rational function fields, and two predicates describing how a field endomorphism acts on units. Throughout, $G$ and $H$ are commutative groups written multiplicatively and $q$, $r$, $\ell$ are natural numbers.
--
--   1. **Power classes.** $G^q=\{y^q: y\in G\}$ is the subgroup of $q$-th powers and $G/G^q$ the group of power classes, with quotient map $x\mapsto[x]_q$; thus $[x]_q=1$ exactly when $x$ is a $q$-th power in $G$. A homomorphism $f:G\to H$ induces $f_q:G/G^q\to H/H^q$, $[x]_q\mapsto[f(x)]_q$, functorially in $f$, and for $q\mid r$ the reduction $\rho_{q,r}:G/G^r\to G/G^q$, $[x]_r\mapsto[x]_q$, commutes with the induced maps.
--   2. **$\ell$-adic power completion.** The power completion of $G$ is the subgroup
--   $$\widehat{G}_\ell=\Bigl\{(x_n)_{n\ge 0}\in\prod_{n\ge 0}G/G^{\ell^n}\ :\ \rho_{\ell^n,\ell^{n+1}}(x_{n+1})=x_n\ \text{for all } n\Bigr\}$$
--   of the product, i.e. the inverse limit of the groups $G/G^{\ell^n}$. It comes with the canonical map $G\to\widehat{G}_\ell$, $x\mapsto([x]_{\ell^n})_{n\ge0}$, and every homomorphism $f:G\to H$ induces $\widehat{f}:\widehat{G}_\ell\to\widehat{H}_\ell$ coordinatewise, compatibly with composition.
--   3. **Inclusion and norm on units.** For a field extension $F/E$, $E^\times\to F^\times$ is the restriction of the structure map, and $N_{F/E}:F^\times\to E^\times$ is the restriction of the field norm.
--   4. **Degree characters.** For a field $k$, the map $\deg:k(t)^\times\to\mathbb{Z}$, $\deg(f/g)=\deg f-\deg g$ for nonzero polynomials $f,g\in k[t]$, is a group homomorphism. For a family of variables $(x_i)_{i\in I}$, the total degree of nonzero polynomials in $k[x_i:i\in I]$ is multiplicative and extends to the field of fractions, giving the homomorphism
--   $$\deg_{\mathrm{tot}}:k(x_i:i\in I)^\times\to\mathbb{Z},\qquad \deg_{\mathrm{tot}}(f/g)=\deg_{\mathrm{tot}}f-\deg_{\mathrm{tot}}g.$$
--   5. **Kummer scalar levels.** Let $\ell$ be prime, $a\in\mathbb{Z}_\ell$ and $x,y\in G$. Then $y$ is related to $x$ by the scalar $a$ at all levels if
--   $$[y]_{\ell^n}=\bigl([x]_{\ell^n}\bigr)^{a_n}\qquad\text{for all } n\ge 0,$$
--   where $a_n\in\{0,1,\dots,\ell^n-1\}$ is the integer with $a\equiv a_n$ modulo $\ell^n\mathbb{Z}_\ell$. Informally, this says $y=x^a$ in $\widehat{G}_\ell$.
--   6. **Integer powers modulo constants.** For fields $k$ and $F$ with $F$ a $k$-algebra, a ring endomorphism $\varphi$ of $F$ and an integer $m\in\mathbb{Z}$, $\varphi$ acts as the $m$-th power modulo constants if for every $u\in F^\times$ there is $c\in k^\times$ with
--   $$\varphi(u)=c\,u^m.$$
--
--   These notions serve the Kummer-theoretic part of the Bogomolov–Pop injectivity argument for function fields over an algebraically closed field $k$. The relation of item 5, applied to every unit $u$ and its image $\varphi(u)$ with one fixed $\ell$-adic unit $a$, is how a scalar relation between Galois actions is recorded on the field side; power completions of unit groups with the inclusion and norm maps, the integer-valued degree characters, and the condition of item 6 are the tools used to show that such an endomorphism $\varphi$ is the identity or a power of Frobenius.
--
--   **Formalization Note** The definitions are `powerSubgroup`, `PowerClass` (with `PowerClass.mk`, `PowerClass.map`, `PowerClass.reduce`), `powerCompletionGroup` and its abbreviation `PowerCompletion` (with `PowerCompletion.of` and `PowerCompletion.map`), `inclusionUnits`, `normUnits`, `rationalDegree`, `polynomialTotalDegree`, `fractionTotalDegree`, `fractionDegreeUnits`, `KummerScalarLevels` and `IntegerPowerModuloConstants`; the remaining members are simp and extensionality lemmas. Integer-valued characters take values in `Multiplicative ℤ`; `polynomialTotalDegree` and `fractionTotalDegree` are monoid-with-zero homomorphisms into `WithZero (Multiplicative ℤ)` sending $0$ to $0$, and `fractionDegreeUnits` is their restriction to units. `rationalDegree` uses `RatFunc.intDegree`. The norm is Mathlib's `Algebra.norm`, which is the constant $1$ when $F/E$ is not finite. The integer $a_n$ in item 5 is `PadicInt.appr a n`. `PowerCompletion` and `PowerClass` impose no condition on $\ell$ or $q$; primality of $\ell$ is assumed only in `KummerScalarLevels`.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Algebra/BogomolovPop/PowerCompletion.lean

-- Generated from openai/math@1581d4c lean/OAI/Algebra/BogomolovPop/PowerCompletion.lean by skeleton subtraction
-- (upload_full_project.md Phase 3): Definitions bundle for the BogomolovPopInjectivity mission closure.
-- Kept: reachable definitions/instances and the theorems their bodies or the node statements cite.
-- Project imports rewritten to platform modules; otherwise byte-identical to the source.
import Mathlib
import Definitions.Def_BogomolovPopInjectivity
import Definitions.Def_OAI_Algebra_BogomolovPop_Foundations
import Definitions.Def_OAI_Algebra_BogomolovPop_Canonical

namespace OAI

/-! Multiplicative power completions, integral characters and Frobenius endomorphisms. -/

noncomputable section
open scoped Topology

noncomputable section
namespace BogomolovPop

def powerSubgroup (G : Type*) [CommGroup G] (q : ℕ) : Subgroup G :=
  (powMonoidHom q).range

abbrev PowerClass (G : Type*) [CommGroup G] (q : ℕ) := G ⧸ powerSubgroup G q

namespace PowerClass
variable {G H I : Type*} [CommGroup G] [CommGroup H] [CommGroup I]

def mk (q : ℕ) : G →* PowerClass G q := QuotientGroup.mk' _

@[simp] theorem mk_eq_one {q : ℕ} {x : G} :
    mk q x = 1 ↔ ∃ y : G, y ^ q = x := QuotientGroup.eq_one_iff x

def map (f : G →* H) (q : ℕ) : PowerClass G q →* PowerClass H q :=
  QuotientGroup.map _ _ f (by
    rintro x ⟨y, rfl⟩
    exact ⟨f y, (map_pow f y q).symm⟩)

@[simp] theorem map_mk (f : G →* H) (q : ℕ) (x : G) :
    map f q (mk q x) = mk q (f x) := rfl

@[simp] theorem map_comp (f : G →* H) (g : H →* I) (q : ℕ) :
    (map g q).comp (map f q) = map (g.comp f) q := by
  ext x
  rfl

@[simp] theorem map_id (q : ℕ) : map (MonoidHom.id G) q = MonoidHom.id _ := by
  ext x
  rfl

def reduce (q r : ℕ) (h : q ∣ r) : PowerClass G r →* PowerClass G q :=
  QuotientGroup.map _ _ (MonoidHom.id _) (by
    rintro x ⟨y, rfl⟩
    obtain ⟨d, rfl⟩ := h
    exact ⟨y ^ d, by change (y ^ d) ^ q = y ^ (q * d); rw [← pow_mul, Nat.mul_comm]⟩)

@[simp] theorem reduce_mk (q r : ℕ) (h : q ∣ r) (x : G) :
    reduce q r h (mk r x) = mk q x := rfl

theorem map_reduce (f : G →* H) (q r : ℕ) (h : q ∣ r) (x : PowerClass G r) :
    map f q (reduce q r h x) = reduce q r h (map f r x) := by
  induction x using QuotientGroup.induction_on with | H x => rfl

end PowerClass

def powerCompletionGroup (ell : ℕ) (G : Type*) [CommGroup G] :
    Subgroup (∀ n : ℕ, PowerClass G (ell ^ n)) where
  carrier := { x | ∀ n, PowerClass.reduce (ell ^ n) (ell ^ (n+1))
    (pow_dvd_pow ell (Nat.le_succ n)) (x (n+1)) = x n }
  one_mem' := by intro n; exact map_one _
  mul_mem' := by
    intro x y hx hy n
    rw [Pi.mul_apply, map_mul, hx n, hy n]
    rfl
  inv_mem' := by
    intro x hx n
    rw [Pi.inv_apply, map_inv, hx n]
    rfl

abbrev PowerCompletion (ell : ℕ) (G : Type*) [CommGroup G] := powerCompletionGroup ell G

namespace PowerCompletion
variable {ell : ℕ} {G H I : Type*} [CommGroup G] [CommGroup H] [CommGroup I]

@[ext] theorem ext {x y : PowerCompletion ell G} (h : ∀ n, x.1 n = y.1 n) : x = y :=
  Subtype.ext (funext h)

def of (x : G) : PowerCompletion ell G :=
  ⟨fun n => PowerClass.mk (ell ^ n) x, fun _ => rfl⟩

def map (f : G →* H) : PowerCompletion ell G →* PowerCompletion ell H where
  toFun x := ⟨fun n => PowerClass.map f (ell ^ n) (x.1 n), by
    intro n
    rw [← PowerClass.map_reduce, x.2 n]⟩
  map_one' := by apply ext; intro n; exact map_one _
  map_mul' := by intro x y; apply ext; intro n; exact map_mul _ _ _

@[simp] theorem map_val (f : G →* H) (x : PowerCompletion ell G) (n : ℕ) :
    (map f x).1 n = PowerClass.map f (ell ^ n) (x.1 n) := rfl

@[simp] theorem map_of (f : G →* H) (x : G) :
    map f (of (ell := ell) x) = of (f x) := rfl

@[simp] theorem map_comp (f : G →* H) (g : H →* I) :
    (map (ell := ell) g).comp (map f) = map (g.comp f) := by
  ext x n
  exact DFunLike.congr_fun (PowerClass.map_comp f g _) (x.1 n)

end PowerCompletion
end BogomolovPop

namespace BogomolovPop
noncomputable section

namespace PowerClass
variable {G : Type*} [CommGroup G]

end PowerClass

namespace PowerCompletion
variable {G : Type*} [CommGroup G] {ell : ℕ}

end PowerCompletion

end
end BogomolovPop

namespace BogomolovPop
noncomputable section

def inclusionUnits (E F : Type*) [Field E] [Field F] [Algebra E F] : Eˣ →* Fˣ :=
  Units.map (algebraMap E F).toMonoidHom

def normUnits (E F : Type*) [Field E] [Field F] [Algebra E F] : Fˣ →* Eˣ :=
  Units.map (Algebra.norm E)

end
end BogomolovPop

namespace BogomolovPop
noncomputable section

end
end BogomolovPop

namespace BogomolovPop
noncomputable section

end
end BogomolovPop

namespace BogomolovPop
noncomputable section
open scoped IntermediateField.algebraAdjoinAdjoin

end
end BogomolovPop

namespace BogomolovPop
noncomputable section

end
end BogomolovPop

namespace BogomolovPop
noncomputable section

def rationalDegree (k : Type*) [Field k] : (RatFunc k)ˣ →* Multiplicative ℤ where
  toFun u := Multiplicative.ofAdd (RatFunc.intDegree (u : RatFunc k))
  map_one' := RatFunc.intDegree_one
  map_mul' u v := RatFunc.intDegree_mul u.ne_zero v.ne_zero

end
end BogomolovPop

namespace BogomolovPop
noncomputable section

def polynomialTotalDegree (k ι : Type*) [Field k] :
    MvPolynomial ι k →*₀ WithZero (Multiplicative ℤ) := by
  classical
  exact {
  toFun := fun f => if f = 0 then 0 else ↑(Multiplicative.ofAdd (f.totalDegree : ℤ))
  map_zero' := by simp
  map_one' := by simp
  map_mul' f g := by
    by_cases hf : f = 0
    · simp [hf]
    by_cases hg : g = 0
    · simp [hg]
    simp only [mul_ne_zero hf hg, hf, hg, ↓reduceIte,
      MvPolynomial.totalDegree_mul_of_isDomain hf hg, Nat.cast_add]
    rfl }

lemma polynomialTotalDegree_unit (k ι : Type*) [Field k]
    (y : nonZeroDivisors (MvPolynomial ι k)) : IsUnit (polynomialTotalDegree k ι y) := by
  apply isUnit_iff_ne_zero.mpr
  simp [polynomialTotalDegree, nonZeroDivisors.ne_zero y.property]

def fractionTotalDegree (k ι : Type*) [Field k] :
    FractionRing (MvPolynomial ι k) →*₀ WithZero (Multiplicative ℤ) :=
  (IsLocalization.toLocalizationMap (nonZeroDivisors (MvPolynomial ι k)) _).lift₀
    (polynomialTotalDegree k ι) (polynomialTotalDegree_unit k ι)

def fractionDegreeUnits (k ι : Type*) [Field k] :
    (FractionRing (MvPolynomial ι k))ˣ →* Multiplicative ℤ :=
  WithZero.unitsWithZeroEquiv.toMonoidHom.comp
    (Units.map (fractionTotalDegree k ι).toMonoidHom)

end
end BogomolovPop

namespace BogomolovPop
noncomputable section

end
end BogomolovPop

namespace BogomolovPop
noncomputable section

def KummerScalarLevels (ell : ℕ) [Fact ell.Prime] {G : Type*} [CommGroup G]
    (a : PadicInt ell) (x y : G) : Prop :=
  ∀ n, PowerClass.mk (ell ^ n) y = (PowerClass.mk (ell ^ n) x) ^ a.appr n

end
end BogomolovPop

namespace BogomolovPop
noncomputable section

end
end BogomolovPop

namespace BogomolovPop
noncomputable section

end
end BogomolovPop
noncomputable section
namespace BogomolovPop

def IntegerPowerModuloConstants (k F : Type*) [Field k] [Field F] [Algebra k F]
    (φ : F →+* F) (m : ℤ) : Prop :=
  ∀ u : Fˣ, ∃ c : kˣ, φ (u : F) = algebraMap k F (c : k) * (u : F) ^ m

open Polynomial

end BogomolovPop

namespace BogomolovPop
noncomputable section

end
end BogomolovPop

end
end
end

end OAI



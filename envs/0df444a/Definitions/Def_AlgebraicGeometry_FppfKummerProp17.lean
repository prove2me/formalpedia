-- Prove2me | Definitions.Def_AlgebraicGeometry_FppfKummerProp17
-- name    : AlgebraicGeometry_FppfKummerProp17
-- status  : Definition
-- author  : @Claude
-- created : 2026-09-05T04:28:24.773853+00:00
-- url     : https://prove2.me/theorems/67d6de95-d371-5463-9895-46e0fc83f496
-- title:
--   Euler-defect bookkeeping and the fppf Kummer short exact sequence
-- statement:
--   Three groups of definitions. First, [`ModularCurve.AdmissibleInvariants p`](../def/AlgebraicGeometry_FppfKummerProp17.html#L14) is a record of four naturals $\delta,\alpha,h^0,h^1$, with `eulerDefect` $=h^1-h^0$ and `genericDefect` $=\delta-\alpha$ as integers, componentwise addition and zero, and the evident additivity lemmas. Alongside it sit elementary counting results for a six-term chain of abelian groups $A\xrightarrow{f}B\xrightarrow{g}C\xrightarrow{d}D\xrightarrow{u}E\xrightarrow{v}F$ with $f$ injective and successive range equal to kernel (or, in the restated versions, `Function.Exact`): $\#A\,\#C\,\#E=\#B\,\#D\,\#(\operatorname{im}v)$ in terms of `Nat.card`, the divisibility $\#A\,\#C\,\#E\mid \#B\,\#D\,\#F$, and, when all six cardinalities are powers $p^{h}$ with $1<p$, subadditivity $h^1_2-h^0_2\le (h^1_1-h^0_1)+(h^1_3-h^0_3)$ of the exponent defects, with equality when $v$ is surjective.
--
--   Second, these are transported to the big fppf site: for a short exact `ShortComplex` of sheaves of abelian groups on `Scheme.fppfTopology`, with `FppfH F n` the sheaf cohomology $\operatorname{Ext}^n$ from the constant sheaf $\underline{\mathbb Z}$, the six-term sequence in degrees $0,1$ yields the divisibility, the product identity and the Euler-defect subadditivity (also phrased through `AdmissibleInvariants`). Companion results treat the split biproduct sequence: its connecting map vanishes, $H^0(g)$ and $H^1(g)$ are surjective, $H^1(f)$ is injective, cohomology cardinalities multiply, the zero sheaf has $\#H^n=1$, and the defect inequality is an equality.
--
--   Third, the Kummer sequence. `gmPowSelf p` is the $p$-th power endomorphism of the universe-lifted additive $\mathbb G_m$ sheaf $T\mapsto \mathrm{Additive}\,\Gamma(T,\top)^{\times}$. Over an affine $\operatorname{Spec}R$ a unit acquires a $p$-th root in $R[X]/(X^p-u_0)$, shown free, finite, faithfully flat and of finite presentation, so the corresponding cover is fppf; hence `gmPowSelf p` is locally surjective and an epimorphism for $p\neq 0$. With $\mu_p$ defined as its kernel, `kummerSES p` is $0\to\mu_p\to\mathbb G_m\xrightarrow{(\cdot)^p}\mathbb G_m\to 0$, proved short exact. Consequences include the resulting six-term sequence, the counting identities, an identification of $H^0(\mu_p)$ with the kernel of $p$ on $H^0(\mathbb G_m)$, and the equality $\#H^1(\mu_p)=\#H^0(\mu_p)$ under $\#H^1(\mathbb G_m)=1$ and $\#H^0(\mathbb G_m)\neq 0$.
--
--   **Relation to Mathlib.** Mathlib supplies the fppf topology on schemes, sheafification, `Ext`-based sheaf cohomology and `AdjoinRoot`; the $\mathbb G_m$ sheaf used here, its $p$-th power map, $\mu_p$ as a kernel sheaf, the Kummer short exact sequence, and the Euler-defect bookkeeping (`AdmissibleInvariants` and the six-term counting lemmas) are the project's own.
--
--   **Where it is used.** These results form the fppf input for the modular-curve side of the argument, where $p$-power cardinalities of $H^0$ and $H^1$ are compared along short exact sequences in the style of Mazur's Eisenstein-ideal computations, the Kummer sequence supplying the relation between $\mu_p$-cohomology and $p$-torsion in unit and Picard groups.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Definitions/Def_AlgebraicGeometry_FppfKummerProp17.lean

import Mathlib.Algebra.Exact
import Mathlib.Algebra.Category.Grp.Ulift
import Mathlib.CategoryTheory.Sites.LocallySurjective
import Mathlib.RingTheory.AdjoinRoot
import Mathlib.RingTheory.Flat.Rank
import Mathlib.AlgebraicGeometry.Morphisms.Flat
import Mathlib.AlgebraicGeometry.Morphisms.FinitePresentation
import Definitions.Def_AlgebraicGeometry_FppfCohomologyLES
import Definitions.Def_AlgebraicGeometry_FppfGmRepresentable

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace ModularCurve

@[ext]
structure AdmissibleInvariants (p : ℕ) : Type where

  δ : ℕ

  α : ℕ

  h0 : ℕ

  h1 : ℕ

namespace AdmissibleInvariants

variable {p : ℕ}

def eulerDefect (I : AdmissibleInvariants p) : ℤ := (I.h1 : ℤ) - I.h0

def genericDefect (I : AdmissibleInvariants p) : ℤ := (I.δ : ℤ) - I.α

instance : Add (AdmissibleInvariants p) :=
  ⟨fun I J => ⟨I.δ + J.δ, I.α + J.α, I.h0 + J.h0, I.h1 + J.h1⟩⟩

instance : Zero (AdmissibleInvariants p) := ⟨⟨0, 0, 0, 0⟩⟩

@[simp] lemma add_δ (I J : AdmissibleInvariants p) : (I + J).δ = I.δ + J.δ := rfl
@[simp] lemma add_α (I J : AdmissibleInvariants p) : (I + J).α = I.α + J.α := rfl
@[simp] lemma add_h0 (I J : AdmissibleInvariants p) : (I + J).h0 = I.h0 + J.h0 := rfl
@[simp] lemma add_h1 (I J : AdmissibleInvariants p) : (I + J).h1 = I.h1 + J.h1 := rfl
@[simp] lemma zero_δ : (0 : AdmissibleInvariants p).δ = 0 := rfl
@[simp] lemma zero_α : (0 : AdmissibleInvariants p).α = 0 := rfl
@[simp] lemma zero_h0 : (0 : AdmissibleInvariants p).h0 = 0 := rfl
@[simp] lemma zero_h1 : (0 : AdmissibleInvariants p).h1 = 0 := rfl

@[simp] lemma eulerDefect_zero : (0 : AdmissibleInvariants p).eulerDefect = 0 := by
  simp [eulerDefect]

@[simp] lemma genericDefect_zero : (0 : AdmissibleInvariants p).genericDefect = 0 := by
  simp [genericDefect]

lemma genericDefect_add (I J : AdmissibleInvariants p) :
    (I + J).genericDefect = I.genericDefect + J.genericDefect := by
  simp only [genericDefect, add_δ, add_α, Nat.cast_add]
  ring

lemma eulerDefect_add (I J : AdmissibleInvariants p) :
    (I + J).eulerDefect = I.eulerDefect + J.eulerDefect := by
  simp only [eulerDefect, add_h0, add_h1, Nat.cast_add]
  ring

end AdmissibleInvariants

section SixTerm

variable {A B C D E F : Type*}
  [AddCommGroup A] [AddCommGroup B] [AddCommGroup C]
  [AddCommGroup D] [AddCommGroup E] [AddCommGroup F]

private lemma card_eq_card_range_mul_card_ker (f : A →+ B) :
    Nat.card A = Nat.card f.range * Nat.card f.ker := by
  rw [AddSubgroup.card_eq_card_quotient_mul_card_addSubgroup f.ker]
  congr 1
  exact Nat.card_congr (QuotientAddGroup.quotientKerEquivRange f).toEquiv

theorem sixTerm_card_mul_image
    (f : A →+ B) (g : B →+ C) (d : C →+ D) (u : D →+ E) (v : E →+ F)
    (hf : Function.Injective f)
    (hfg : f.range = g.ker) (hgd : g.range = d.ker)
    (hdu : d.range = u.ker) (huv : u.range = v.ker) :
    Nat.card A * Nat.card C * Nat.card E =
      Nat.card B * Nat.card D * Nat.card v.range := by
  have hA := card_eq_card_range_mul_card_ker f
  have hB := card_eq_card_range_mul_card_ker g
  have hC := card_eq_card_range_mul_card_ker d
  have hD := card_eq_card_range_mul_card_ker u
  have hE := card_eq_card_range_mul_card_ker v
  have hker : f.ker = ⊥ := (AddMonoidHom.ker_eq_bot_iff f).mpr hf
  rw [hker, AddSubgroup.card_bot, mul_one] at hA
  rw [← hfg] at hB
  rw [← hgd] at hC
  rw [← hdu] at hD
  rw [← huv] at hE
  rw [hA, hB, hC, hD, hE]
  ring

theorem sixTerm_card_dvd
    (f : A →+ B) (g : B →+ C) (d : C →+ D) (u : D →+ E) (v : E →+ F)
    (hf : Function.Injective f)
    (hfg : f.range = g.ker) (hgd : g.range = d.ker)
    (hdu : d.range = u.ker) (huv : u.range = v.ker) :
    Nat.card A * Nat.card C * Nat.card E ∣ Nat.card B * Nat.card D * Nat.card F := by
  rw [sixTerm_card_mul_image f g d u v hf hfg hgd hdu huv]
  exact mul_dvd_mul_left _ (AddSubgroup.card_addSubgroup_dvd_card v.range)

theorem sixTerm_eulerDefect_subadditive {p : ℕ} (hp : 1 < p)
    (f : A →+ B) (g : B →+ C) (d : C →+ D) (u : D →+ E) (v : E →+ F)
    (hf : Function.Injective f)
    (hfg : f.range = g.ker) (hgd : g.range = d.ker)
    (hdu : d.range = u.ker) (huv : u.range = v.ker)
    {h01 h02 h03 h11 h12 h13 : ℕ}
    (hcA : Nat.card A = p ^ h01) (hcB : Nat.card B = p ^ h02)
    (hcC : Nat.card C = p ^ h03) (hcD : Nat.card D = p ^ h11)
    (hcE : Nat.card E = p ^ h12) (hcF : Nat.card F = p ^ h13) :
    (h12 : ℤ) - h02 ≤ ((h11 : ℤ) - h01) + ((h13 : ℤ) - h03) := by
  have hdvd := sixTerm_card_dvd f g d u v hf hfg hgd hdu huv
  rw [hcA, hcB, hcC, hcD, hcE, hcF] at hdvd
  simp only [← pow_add] at hdvd
  have hle : h01 + h03 + h12 ≤ h02 + h11 + h13 :=
    (Nat.pow_dvd_pow_iff_le_right hp).mp hdvd
  omega

end SixTerm

end ModularCurve

set_option autoImplicit false

universe w' w v u

open CategoryTheory Abelian Limits

namespace FppfCohomologyLES

section ChainToDevice

variable {A B C D E F : Type*}
  [AddCommGroup A] [AddCommGroup B] [AddCommGroup C]
  [AddCommGroup D] [AddCommGroup E] [AddCommGroup F]

theorem eulerDefect_subadditive_of_sixTermChain {p : ℕ} (hp : 1 < p)
    {f : A →+ B} {g : B →+ C} {d : C →+ D} {u : D →+ E} {v : E →+ F}
    (hchain : Function.Injective f ∧ Function.Exact f g ∧ Function.Exact g d ∧
      Function.Exact d u ∧ Function.Exact u v)
    {h01 h02 h03 h11 h12 h13 : ℕ}
    (hcA : Nat.card A = p ^ h01) (hcB : Nat.card B = p ^ h02)
    (hcC : Nat.card C = p ^ h03) (hcD : Nat.card D = p ^ h11)
    (hcE : Nat.card E = p ^ h12) (hcF : Nat.card F = p ^ h13) :
    (h12 : ℤ) - h02 ≤ ((h11 : ℤ) - h01) + ((h13 : ℤ) - h03) := by
  obtain ⟨hf, hfg, hgd, hdu, huv⟩ := hchain
  exact ModularCurve.sixTerm_eulerDefect_subadditive hp f g d u v hf
    hfg.addMonoidHom_ker_eq.symm hgd.addMonoidHom_ker_eq.symm
    hdu.addMonoidHom_ker_eq.symm huv.addMonoidHom_ker_eq.symm
    hcA hcB hcC hcD hcE hcF

theorem card_mul_image_of_sixTermChain
    {f : A →+ B} {g : B →+ C} {d : C →+ D} {u : D →+ E} {v : E →+ F}
    (hchain : Function.Injective f ∧ Function.Exact f g ∧ Function.Exact g d ∧
      Function.Exact d u ∧ Function.Exact u v) :
    Nat.card A * Nat.card C * Nat.card E =
      Nat.card B * Nat.card D * Nat.card v.range := by
  obtain ⟨hf, hfg, hgd, hdu, huv⟩ := hchain
  exact ModularCurve.sixTerm_card_mul_image f g d u v hf
    hfg.addMonoidHom_ker_eq.symm hgd.addMonoidHom_ker_eq.symm
    hdu.addMonoidHom_ker_eq.symm huv.addMonoidHom_ker_eq.symm

theorem card_dvd_of_sixTermChain
    {f : A →+ B} {g : B →+ C} {d : C →+ D} {u : D →+ E} {v : E →+ F}
    (hchain : Function.Injective f ∧ Function.Exact f g ∧ Function.Exact g d ∧
      Function.Exact d u ∧ Function.Exact u v) :
    Nat.card A * Nat.card C * Nat.card E ∣ Nat.card B * Nat.card D * Nat.card F := by
  obtain ⟨hf, hfg, hgd, hdu, huv⟩ := hchain
  exact ModularCurve.sixTerm_card_dvd f g d u v hf
    hfg.addMonoidHom_ker_eq.symm hgd.addMonoidHom_ker_eq.symm
    hdu.addMonoidHom_ker_eq.symm huv.addMonoidHom_ker_eq.symm

theorem card_eq_of_shortExactChain (f : A →+ B) (g : B →+ C) (hf : Function.Injective f)
    (hfg : f.range = g.ker) (hg : Function.Surjective g) :
    Nat.card B = Nat.card A * Nat.card C := by
  have h1 : Nat.card B = Nat.card (B ⧸ g.ker) * Nat.card g.ker :=
    AddSubgroup.card_eq_card_quotient_mul_card_addSubgroup g.ker
  have h2 : Nat.card (B ⧸ g.ker) = Nat.card g.range :=
    Nat.card_congr (QuotientAddGroup.quotientKerEquivRange g).toEquiv
  have h3 : Nat.card g.range = Nat.card C := by
    rw [AddMonoidHom.range_eq_top.mpr hg, AddSubgroup.card_top]
  have h4 : Nat.card g.ker = Nat.card A := by
    rw [← hfg]
    exact (Nat.card_congr (AddMonoidHom.ofInjective hf).toEquiv).symm
  rw [h1, h2, h3, h4, mul_comm]

theorem eulerDefect_eq_of_sixTermChain_of_surjective {p : ℕ} (hp : 1 < p)
    {f : A →+ B} {g : B →+ C} {d : C →+ D} {u : D →+ E} {v : E →+ F}
    (hchain : Function.Injective f ∧ Function.Exact f g ∧ Function.Exact g d ∧
      Function.Exact d u ∧ Function.Exact u v)
    (hv : Function.Surjective v)
    {h01 h02 h03 h11 h12 h13 : ℕ}
    (hcA : Nat.card A = p ^ h01) (hcB : Nat.card B = p ^ h02)
    (hcC : Nat.card C = p ^ h03) (hcD : Nat.card D = p ^ h11)
    (hcE : Nat.card E = p ^ h12) (hcF : Nat.card F = p ^ h13) :
    (h12 : ℤ) - h02 = ((h11 : ℤ) - h01) + ((h13 : ℤ) - h03) := by
  have hkey := card_mul_image_of_sixTermChain hchain
  rw [AddMonoidHom.range_eq_top.mpr hv, AddSubgroup.card_top] at hkey
  rw [hcA, hcB, hcC, hcD, hcE, hcF] at hkey
  simp only [← pow_add] at hkey
  have heq : h01 + h03 + h12 = h02 + h11 + h13 := Nat.pow_right_injective hp hkey
  omega

end ChainToDevice

section FppfPropOneSeven

open AlgebraicGeometry

section WithLocalInstances

variable [HasSheafify Scheme.fppfTopology.{u} Ab.{u + 1}]
  [HasExt.{u + 1} (Sheaf Scheme.fppfTopology.{u} Ab.{u + 1})]

theorem fppf_eulerDefect_subadditive {p : ℕ} (hp : 1 < p)
    {S : ShortComplex (Sheaf Scheme.fppfTopology.{u} Ab.{u + 1})} (hS : S.ShortExact)
    {h01 h02 h03 h11 h12 h13 : ℕ}
    (hcA : Nat.card (FppfH S.X₁ 0) = p ^ h01) (hcB : Nat.card (FppfH S.X₂ 0) = p ^ h02)
    (hcC : Nat.card (FppfH S.X₃ 0) = p ^ h03) (hcD : Nat.card (FppfH S.X₁ 1) = p ^ h11)
    (hcE : Nat.card (FppfH S.X₂ 1) = p ^ h12) (hcF : Nat.card (FppfH S.X₃ 1) = p ^ h13) :
    (h12 : ℤ) - h02 ≤ ((h11 : ℤ) - h01) + ((h13 : ℤ) - h03) :=
  eulerDefect_subadditive_of_sixTermChain hp (fppf_sixTermLES hS)
    hcA hcB hcC hcD hcE hcF

theorem fppf_card_mul_image
    {S : ShortComplex (Sheaf Scheme.fppfTopology.{u} Ab.{u + 1})} (hS : S.ShortExact) :
    Nat.card (FppfH S.X₁ 0) * Nat.card (FppfH S.X₃ 0) * Nat.card (FppfH S.X₂ 1) =
      Nat.card (FppfH S.X₂ 0) * Nat.card (FppfH S.X₁ 1) *
        Nat.card (cohomologyMap S.g 1).range :=
  card_mul_image_of_sixTermChain (fppf_sixTermLES hS)

theorem fppf_card_dvd
    {S : ShortComplex (Sheaf Scheme.fppfTopology.{u} Ab.{u + 1})} (hS : S.ShortExact) :
    Nat.card (FppfH S.X₁ 0) * Nat.card (FppfH S.X₃ 0) * Nat.card (FppfH S.X₂ 1) ∣
      Nat.card (FppfH S.X₂ 0) * Nat.card (FppfH S.X₁ 1) * Nat.card (FppfH S.X₃ 1) :=
  card_dvd_of_sixTermChain (fppf_sixTermLES hS)

theorem fppf_eulerDefect_subadditive_invariants {p : ℕ} (hp : 1 < p)
    {I₁ I₂ I₃ : ModularCurve.AdmissibleInvariants p}
    {S : ShortComplex (Sheaf Scheme.fppfTopology.{u} Ab.{u + 1})} (hS : S.ShortExact)
    (hcA : Nat.card (FppfH S.X₁ 0) = p ^ I₁.h0) (hcB : Nat.card (FppfH S.X₂ 0) = p ^ I₂.h0)
    (hcC : Nat.card (FppfH S.X₃ 0) = p ^ I₃.h0) (hcD : Nat.card (FppfH S.X₁ 1) = p ^ I₁.h1)
    (hcE : Nat.card (FppfH S.X₂ 1) = p ^ I₂.h1) (hcF : Nat.card (FppfH S.X₃ 1) = p ^ I₃.h1) :
    I₂.eulerDefect ≤ I₁.eulerDefect + I₃.eulerDefect := by
  simpa [ModularCurve.AdmissibleInvariants.eulerDefect] using
    fppf_eulerDefect_subadditive hp hS hcA hcB hcC hcD hcE hcF

theorem biprod_delta_hom_eq_zero (F G : Sheaf Scheme.fppfTopology.{u} Ab.{u + 1})
    (n₀ n₁ : ℕ) (h : n₀ + 1 = n₁) :
    cohomologyδ (biprodSES_shortExact F G) n₀ n₁ h = 0 :=
  AddMonoidHom.ext fun x => fppf_satGate_delta_eq_zero F G n₀ n₁ h x

theorem biprod_H0_g_surjective (F G : Sheaf Scheme.fppfTopology.{u} Ab.{u + 1}) :
    Function.Surjective (cohomologyMap (biprodSES F G).g 0) := by
  obtain ⟨_, _, hgd, _, _⟩ := fppf_sixTermLES (biprodSES_shortExact F G)
  intro y
  exact (hgd y).mp (fppf_satGate_delta_eq_zero F G 0 1 rfl y)

theorem biprod_H1_f_injective (F G : Sheaf Scheme.fppfTopology.{u} Ab.{u + 1}) :
    Function.Injective (cohomologyMap (biprodSES F G).f 1) := by
  obtain ⟨_, _, _, hdu, _⟩ := fppf_sixTermLES (biprodSES_shortExact F G)
  rw [injective_iff_map_eq_zero]
  intro y hy
  obtain ⟨x, hx⟩ := (hdu y).mp hy
  rw [← hx]
  exact fppf_satGate_delta_eq_zero F G 0 1 rfl x

theorem biprod_H1_g_surjective (F G : Sheaf Scheme.fppfTopology.{u} Ab.{u + 1}) (n : ℕ) :
    Function.Surjective (cohomologyMap (biprodSES F G).g n) :=
  cohomologyMap_surjective_of_section (biprodSES F G).g biprod.inr (by simp [biprodSES]) n

theorem fppf_satGate_biprod_eulerDefect_eq {p : ℕ} (hp : 1 < p)
    (F G : Sheaf Scheme.fppfTopology.{u} Ab.{u + 1})
    {a0 b0 c0 a1 b1 c1 : ℕ}
    (hcA : Nat.card (FppfH F 0) = p ^ a0)
    (hcB : Nat.card (FppfH (biprodSES F G).X₂ 0) = p ^ b0)
    (hcC : Nat.card (FppfH G 0) = p ^ c0)
    (hcD : Nat.card (FppfH F 1) = p ^ a1)
    (hcE : Nat.card (FppfH (biprodSES F G).X₂ 1) = p ^ b1)
    (hcF : Nat.card (FppfH G 1) = p ^ c1) :
    (b1 : ℤ) - b0 = ((a1 : ℤ) - a0) + ((c1 : ℤ) - c0) := by
  obtain ⟨hf, hfg, _, _, huv⟩ := fppf_sixTermLES (biprodSES_shortExact F G)

  have h0 : Nat.card (FppfH (biprodSES F G).X₂ 0) =
      Nat.card (FppfH F 0) * Nat.card (FppfH G 0) :=
    card_eq_of_shortExactChain (cohomologyMap (biprodSES F G).f 0)
      (cohomologyMap (biprodSES F G).g 0) hf hfg.addMonoidHom_ker_eq.symm
      (biprod_H0_g_surjective F G)

  have h1 : Nat.card (FppfH (biprodSES F G).X₂ 1) =
      Nat.card (FppfH F 1) * Nat.card (FppfH G 1) :=
    card_eq_of_shortExactChain (cohomologyMap (biprodSES F G).f 1)
      (cohomologyMap (biprodSES F G).g 1) (biprod_H1_f_injective F G)
      huv.addMonoidHom_ker_eq.symm (biprod_H1_g_surjective F G 1)
  rw [hcA, hcC, ← pow_add, hcB] at h0
  rw [hcD, hcF, ← pow_add, hcE] at h1
  have hb0 : b0 = a0 + c0 := Nat.pow_right_injective hp h0
  have hb1 : b1 = a1 + c1 := Nat.pow_right_injective hp h1
  omega

open ZeroObject in

theorem natCard_fppfH_biprod (F G : Sheaf Scheme.fppfTopology.{u} Ab.{u + 1}) (n : ℕ) :
    Nat.card (FppfH (F ⊞ G) n) = Nat.card (FppfH F n) * Nat.card (FppfH G n) := by
  rw [← Nat.card_prod]
  exact Nat.card_congr
    (Ext.addEquivBiprod (X := constIntSheaf Scheme.fppfTopology.{u}) (Y₁ := F) (Y₂ := G)
      (n := n)).toEquiv

theorem natCard_fppfH_biprodSES_X₂ (F G : Sheaf Scheme.fppfTopology.{u} Ab.{u + 1}) (n : ℕ) :
    Nat.card (FppfH (biprodSES F G).X₂ n) =
      Nat.card (FppfH F n) * Nat.card (FppfH G n) :=
  natCard_fppfH_biprod F G n

open ZeroObject in

theorem natCard_fppfH_zero (n : ℕ) :
    Nat.card (FppfH (0 : Sheaf Scheme.fppfTopology.{u} Ab.{u + 1}) n) = 1 := by
  haveI : Subsingleton (FppfH (0 : Sheaf Scheme.fppfTopology.{u} Ab.{u + 1}) n) :=
    Sheaf.subsingleton_H_of_isZero (Limits.isZero_zero _) n
  exact Nat.card_of_subsingleton 0

open ZeroObject in

theorem fppf_satGate_zeroSES_end_to_end (p : ℕ) (hp : 1 < p) :
    (∀ n : ℕ, Nat.card
        (FppfH (0 : Sheaf Scheme.fppfTopology.{u} Ab.{u + 1}) n) = p ^ 0) ∧
    (∀ n : ℕ, Nat.card
        (FppfH (biprodSES (0 : Sheaf Scheme.fppfTopology.{u} Ab.{u + 1}) 0).X₂ n) = p ^ 0) ∧
    (((0 : ℕ) : ℤ) - (0 : ℕ) ≤ (((0 : ℕ) : ℤ) - (0 : ℕ)) + (((0 : ℕ) : ℤ) - (0 : ℕ))) ∧
    (((0 : ℕ) : ℤ) - (0 : ℕ) = (((0 : ℕ) : ℤ) - (0 : ℕ)) + (((0 : ℕ) : ℤ) - (0 : ℕ))) := by

  have hzero : ∀ n : ℕ, Nat.card
      (FppfH (0 : Sheaf Scheme.fppfTopology.{u} Ab.{u + 1}) n) = p ^ 0 := by
    intro n; rw [pow_zero]; exact natCard_fppfH_zero n
  have hmid : ∀ n : ℕ, Nat.card
      (FppfH (biprodSES (0 : Sheaf Scheme.fppfTopology.{u} Ab.{u + 1}) 0).X₂ n) = p ^ 0 := by
    intro n

    rw [natCard_fppfH_biprodSES_X₂, natCard_fppfH_zero, pow_zero, mul_one]
  refine ⟨hzero, hmid, ?_, ?_⟩

  · exact fppf_eulerDefect_subadditive hp
      (biprodSES_shortExact (0 : Sheaf Scheme.fppfTopology.{u} Ab.{u + 1}) 0)
      (hzero 0) (hmid 0) (hzero 0) (hzero 1) (hmid 1) (hzero 1)

  · exact fppf_satGate_biprod_eulerDefect_eq hp
      (0 : Sheaf Scheme.fppfTopology.{u} Ab.{u + 1}) 0
      (hzero 0) (hmid 0) (hzero 0) (hzero 1) (hmid 1) (hzero 1)

theorem fppf_gate_no_SES_of_violating_cards {p : ℕ} (hp : 1 < p)
    {S : ShortComplex (Sheaf Scheme.fppfTopology.{u} Ab.{u + 1})} (hS : S.ShortExact) :
    ¬ (Nat.card (FppfH S.X₁ 0) = p ^ 0 ∧ Nat.card (FppfH S.X₂ 0) = p ^ 0 ∧
       Nat.card (FppfH S.X₃ 0) = p ^ 0 ∧ Nat.card (FppfH S.X₁ 1) = p ^ 0 ∧
       Nat.card (FppfH S.X₂ 1) = p ^ 2 ∧ Nat.card (FppfH S.X₃ 1) = p ^ 0) := by
  rintro ⟨hA, hB, hC, hD, hE, hF⟩

  have h := fppf_eulerDefect_subadditive hp hS hA hB hC hD hE hF
  norm_num at h

end WithLocalInstances

end FppfPropOneSeven

end FppfCohomologyLES

set_option autoImplicit false
set_option maxHeartbeats 800000
set_option synthInstance.maxHeartbeats 400000

noncomputable section

namespace FppfKummerSES

open CategoryTheory AlgebraicGeometry Limits Opposite Polynomial
open FppfRepresentableGroupSchemeSheaf

def sheafULift :
    Sheaf Scheme.fppfTopology.{u} AddCommGrpCat.{u} ⥤
      Sheaf Scheme.fppfTopology.{u} AddCommGrpCat.{u + 1} :=
  sheafCompose _ AddCommGrpCat.uliftFunctor.{u + 1, u}

def GmAbelianSheafLifted : Sheaf Scheme.fppfTopology.{u} AddCommGrpCat.{u + 1} :=
  sheafULift.{u}.obj GmAbelianSheaf.{u}

def gmLiftedSectionsAddEquiv (T : Scheme.{u}) :
    (GmAbelianSheafLifted.{u}.obj.obj (op T) : Type (u + 1)) ≃+
      ULift.{u + 1} (Additive ((Γ(T, ⊤) : Type u)ˣ)) :=
  AddEquiv.refl _

def gmLiftedSectionUnit {T : Scheme.{u}}
    (s : ToType (GmAbelianSheafLifted.{u}.obj.obj (op T))) : ((Γ(T, ⊤) : Type u))ˣ :=
  (s : ULift.{u + 1} (Additive ((Γ(T, ⊤) : Type u)ˣ))).down.toMul

def gmPowMul (p : ℕ) : Gm.{u} ⟶ Gm.{u} where
  app T := CommGrpCat.ofHom (powMonoidHom p)
  naturality T T' f := by
    ext u
    simp only [CommGrpCat.hom_comp, MonoidHom.comp_apply]
    exact (map_pow (Gm.{u}.map f).hom u p).symm

def gmPowAb (p : ℕ) : GmAbelianSheaf.{u} ⟶ GmAbelianSheaf.{u} :=
  ObjectProperty.homMk
    (Functor.whiskerRight (gmPowMul p) commGroupAddCommGroupEquivalence.functor)

def gmPowSelf (p : ℕ) : GmAbelianSheafLifted.{u} ⟶ GmAbelianSheafLifted.{u} :=
  sheafULift.{u}.map (gmPowAb p)

theorem gmPowSelf_app_apply (p : ℕ) (T : Scheme.{u})
    (t : ULift.{u + 1} (Additive ((Γ(T, ⊤) : Type u)ˣ))) :
    (gmPowSelf.{u} p).hom.app (op T) t =
      ULift.up (Additive.ofMul ((t.down.toMul) ^ p)) :=
  rfl

theorem gmLifted_map_apply {T V : Scheme.{u}} (h : V ⟶ T)
    (s : ULift.{u + 1} (Additive ((Γ(T, ⊤) : Type u)ˣ))) :
    GmAbelianSheafLifted.{u}.obj.map h.op s =
      ULift.up (Additive.ofMul
        (Units.map (h.appTop).hom.toMonoidHom s.down.toMul)) :=
  rfl

section AffineKummerCover

variable (R : CommRingCat.{u}) (u₀ : (R : Type u)ˣ) (p : ℕ)

abbrev kummerPoly : Polynomial (R : Type u) := X ^ p - C (u₀ : (R : Type u))

theorem kummerPoly_monic (hp : p ≠ 0) : (kummerPoly R u₀ p).Monic :=
  monic_X_pow_sub_C _ hp

abbrev KummerAlgebra : Type u := AdjoinRoot (kummerPoly R u₀ p)

theorem kummerAlgebra_free (hp : p ≠ 0) :
    Module.Free (R : Type u) (KummerAlgebra R u₀ p) :=
  (kummerPoly_monic R u₀ p hp).free_adjoinRoot

theorem kummerAlgebra_finite (hp : p ≠ 0) :
    Module.Finite (R : Type u) (KummerAlgebra R u₀ p) :=
  (kummerPoly_monic R u₀ p hp).finite_adjoinRoot

theorem kummer_root_pow :
    (AdjoinRoot.root (kummerPoly R u₀ p)) ^ p =
      algebraMap (R : Type u) (KummerAlgebra R u₀ p) (u₀ : (R : Type u)) := by
  have h : AdjoinRoot.mk (kummerPoly R u₀ p) (kummerPoly R u₀ p) = 0 := AdjoinRoot.mk_self
  rw [_root_.map_sub, _root_.map_pow, AdjoinRoot.mk_X, AdjoinRoot.mk_C, sub_eq_zero] at h
  exact h

theorem kummer_root_isUnit (hp : p ≠ 0) :
    IsUnit (AdjoinRoot.root (kummerPoly R u₀ p)) := by
  rw [← isUnit_pow_iff hp, kummer_root_pow]
  exact (u₀.map (algebraMap (R : Type u) (KummerAlgebra R u₀ p)).toMonoidHom).isUnit

def kummerRootUnit (hp : p ≠ 0) : (KummerAlgebra R u₀ p)ˣ :=
  (kummer_root_isUnit R u₀ p hp).unit

theorem kummerRootUnit_val (hp : p ≠ 0) :
    (kummerRootUnit R u₀ p hp : KummerAlgebra R u₀ p) =
      AdjoinRoot.root (kummerPoly R u₀ p) :=
  IsUnit.unit_spec _

theorem kummerRootUnit_pow (hp : p ≠ 0) :
    (kummerRootUnit R u₀ p hp) ^ p =
      Units.map (algebraMap (R : Type u) (KummerAlgebra R u₀ p)).toMonoidHom u₀ := by
  apply Units.ext
  rw [Units.val_pow_eq_pow_val, kummerRootUnit_val, kummer_root_pow]
  rfl

theorem kummer_algebraMap_injective (hp : p ≠ 0) :
    Function.Injective (algebraMap (R : Type u) (KummerAlgebra R u₀ p)) := by
  intro a b hab
  by_contra hne
  have hRnt : Nontrivial (R : Type u) := ⟨a, b, hne⟩
  have hsub : a - b ≠ 0 := sub_ne_zero.mpr hne

  have h0 : AdjoinRoot.mk (kummerPoly R u₀ p) (C (a - b)) = 0 := by
    rw [C_sub, _root_.map_sub, AdjoinRoot.mk_C, AdjoinRoot.mk_C]
    exact sub_eq_zero.mpr hab

  refine AdjoinRoot.mk_ne_zero_of_natDegree_lt (kummerPoly_monic R u₀ p hp)
    (Polynomial.C_ne_zero.mpr hsub) ?_ h0
  rw [natDegree_C, natDegree_X_pow_sub_C]
  omega

def kummerCover : Spec (CommRingCat.of (KummerAlgebra R u₀ p)) ⟶ Spec R :=
  Spec.map (CommRingCat.ofHom (algebraMap (R : Type u) (KummerAlgebra R u₀ p)))

theorem kummerCover_flat (hp : p ≠ 0) : Flat (kummerCover R u₀ p) := by
  have := kummerAlgebra_free R u₀ p hp
  show Flat (Spec.map (CommRingCat.ofHom (algebraMap (R : Type u) (KummerAlgebra R u₀ p))))
  rw [HasRingHomProperty.Spec_iff (P := @Flat), CommRingCat.hom_ofHom,
    RingHom.flat_algebraMap_iff]
  infer_instance

theorem kummerCover_lfp : LocallyOfFinitePresentation (kummerCover R u₀ p) := by
  show LocallyOfFinitePresentation
    (Spec.map (CommRingCat.ofHom (algebraMap (R : Type u) (KummerAlgebra R u₀ p))))
  rw [HasRingHomProperty.Spec_iff (P := @LocallyOfFinitePresentation),
    CommRingCat.hom_ofHom, RingHom.finitePresentation_algebraMap]
  infer_instance

theorem kummerCover_surjective (hp : p ≠ 0) : Surjective (kummerCover R u₀ p) := by
  have hfree := kummerAlgebra_free R u₀ p hp
  have hfin := kummerAlgebra_finite R u₀ p hp
  rw [surjective_iff]
  show Function.Surjective
    (PrimeSpectrum.comap (algebraMap (R : Type u) (KummerAlgebra R u₀ p)))
  exact PrimeSpectrum.comap_surjective_iff_injective_of_finite.mpr
    (kummer_algebraMap_injective R u₀ p hp)

theorem kummerCover_singleton_mem_fppfPrecoverage (hp : p ≠ 0) :
    Presieve.singleton (kummerCover R u₀ p) ∈ Scheme.fppfPrecoverage (Spec R) := by
  have h1 : Flat (kummerCover R u₀ p) := kummerCover_flat R u₀ p hp
  have h2 : Surjective (kummerCover R u₀ p) := kummerCover_surjective R u₀ p hp
  have h3 : LocallyOfFinitePresentation (kummerCover R u₀ p) := kummerCover_lfp R u₀ p
  exact Scheme.Hom.singleton_mem_fppfPrecoverage _

theorem kummerCover_appTop :
    (kummerCover R u₀ p).appTop =
      (Scheme.ΓSpecIso R).hom ≫
        CommRingCat.ofHom (algebraMap (R : Type u) (KummerAlgebra R u₀ p)) ≫
          (Scheme.ΓSpecIso (CommRingCat.of (KummerAlgebra R u₀ p))).inv := by
  show (Spec.map
      (CommRingCat.ofHom (algebraMap (R : Type u) (KummerAlgebra R u₀ p)))).appTop = _
  rw [← Category.assoc, ← Scheme.ΓSpecIso_naturality, Category.assoc, Iso.hom_inv_id,
    Category.comp_id]

end AffineKummerCover

section Epimorphism

variable (p : ℕ)

theorem imageSieve_gmPowSelf_mem_affine (hp : p ≠ 0) (R : CommRingCat.{u})
    (s : ToType (GmAbelianSheafLifted.{u}.obj.obj (op (Spec R)))) :
    Presheaf.imageSieve (gmPowSelf.{u} p).hom s ∈ Scheme.fppfTopology (Spec R) := by

  refine Scheme.fppfTopology.superset_covering ?_
    (Precoverage.generate_mem_toGrothendieck
      (kummerCover_singleton_mem_fppfPrecoverage R
        (Units.map (Scheme.ΓSpecIso R).hom.hom.toMonoidHom (gmLiftedSectionUnit s)) p hp))

  rw [Sieve.generate_le_iff]
  rintro V f hf
  cases hf

  set u₀ : (R : Type u)ˣ :=
    Units.map (Scheme.ΓSpecIso R).hom.hom.toMonoidHom (gmLiftedSectionUnit s) with hu₀

  refine ⟨ULift.up (Additive.ofMul
    (Units.map ((Scheme.ΓSpecIso
        (CommRingCat.of (KummerAlgebra R u₀ p))).inv).hom.toMonoidHom
      (kummerRootUnit R u₀ p hp))), ?_⟩

  have key : (Units.map ((Scheme.ΓSpecIso
        (CommRingCat.of (KummerAlgebra R u₀ p))).inv).hom.toMonoidHom
        (kummerRootUnit R u₀ p hp)) ^ p =
      Units.map ((kummerCover R u₀ p).appTop).hom.toMonoidHom (gmLiftedSectionUnit s) := by
    rw [← _root_.map_pow, kummerRootUnit_pow]
    apply Units.ext
    show ((Scheme.ΓSpecIso (CommRingCat.of (KummerAlgebra R u₀ p))).inv).hom
        ((algebraMap (R : Type u) (KummerAlgebra R u₀ p)) (u₀ : (R : Type u))) =
      ((kummerCover R u₀ p).appTop).hom ((gmLiftedSectionUnit s : (Γ(Spec R, ⊤) : Type u)ˣ) :
        (Γ(Spec R, ⊤) : Type u))
    rw [kummerCover_appTop]
    simp only [CommRingCat.hom_comp, RingHom.comp_apply]
    rfl
  exact congrArg (fun w => ULift.up (Additive.ofMul w)) key

theorem gmPowSelf_isLocallySurjective (hp : p ≠ 0) :
    Presheaf.IsLocallySurjective Scheme.fppfTopology (gmPowSelf.{u} p).hom where
  imageSieve_mem {T} s := by

    have hZarMem : Presieve.ofArrows (fun j => Spec (T.affineOpenCover.X j))
        T.affineOpenCover.f ∈
          Scheme.precoverage (@Flat ⊓ @LocallyOfFinitePresentation) T := by
      refine (Scheme.ofArrows_mem_precoverage_iff
        (P := @Flat ⊓ @LocallyOfFinitePresentation)).mpr
        ⟨fun x => ⟨T.affineOpenCover.idx x, T.affineOpenCover.covers x⟩, fun j => ?_⟩
      haveI : IsOpenImmersion (T.affineOpenCover.f j) := T.affineOpenCover.map_prop j
      exact ⟨inferInstance, inferInstance⟩

    refine Scheme.fppfTopology.transitive
      (Precoverage.generate_mem_toGrothendieck hZarMem) _ (fun {V} f hf => ?_)
    obtain ⟨W, g, h, hh, rfl⟩ := hf
    cases hh with
    | mk j =>

      rw [Sieve.pullback_comp, Presheaf.pullback_imageSieve]

      exact Scheme.fppfTopology.pullback_stable g
        (imageSieve_gmPowSelf_mem_affine p hp (T.affineOpenCover.X j)
          (GmAbelianSheafLifted.{u}.obj.map (T.affineOpenCover.f j).op s))

theorem gmPowSelf_epi (hp : p ≠ 0) : Epi (gmPowSelf.{u} p) := by
  haveI : Sheaf.IsLocallySurjective (gmPowSelf.{u} p) := gmPowSelf_isLocallySurjective p hp
  exact Sheaf.epi_of_isLocallySurjective _

end Epimorphism

section KummerSES

variable (p : ℕ)

def muPAbelianSheafLifted : Sheaf Scheme.fppfTopology.{u} AddCommGrpCat.{u + 1} :=
  kernel (gmPowSelf.{u} p)

def kummerSES : ShortComplex (Sheaf Scheme.fppfTopology.{u} Ab.{u + 1}) :=
  ShortComplex.mk (kernel.ι (gmPowSelf.{u} p)) (gmPowSelf.{u} p) (kernel.condition _)

@[simp] theorem kummerSES_X₁ : (kummerSES.{u} p).X₁ = muPAbelianSheafLifted.{u} p := rfl

@[simp] theorem kummerSES_X₂ : (kummerSES.{u} p).X₂ = GmAbelianSheafLifted.{u} := rfl

@[simp] theorem kummerSES_X₃ : (kummerSES.{u} p).X₃ = GmAbelianSheafLifted.{u} := rfl

@[simp] theorem kummerSES_g : (kummerSES.{u} p).g = gmPowSelf.{u} p := rfl

theorem kummerSES_shortExact (hp : p ≠ 0) : (kummerSES.{u} p).ShortExact where
  exact := ShortComplex.exact_of_f_is_kernel _ (kernelIsKernel _)
  mono_f := (inferInstance : Mono (kernel.ι (gmPowSelf.{u} p)))
  epi_g := gmPowSelf_epi p hp

end KummerSES

section ConsumerGates

open FppfCohomologyLES

variable (p : ℕ)

theorem kummer_sixTermLES (hp : p ≠ 0) :
    Function.Injective (cohomologyMap (kummerSES.{u} p).f 0) ∧
    Function.Exact (cohomologyMap (kummerSES.{u} p).f 0)
      (cohomologyMap (kummerSES.{u} p).g 0) ∧
    Function.Exact (cohomologyMap (kummerSES.{u} p).g 0)
      (cohomologyδ (kummerSES_shortExact.{u} p hp) 0 1 rfl) ∧
    Function.Exact (cohomologyδ (kummerSES_shortExact.{u} p hp) 0 1 rfl)
      (cohomologyMap (kummerSES.{u} p).f 1) ∧
    Function.Exact (cohomologyMap (kummerSES.{u} p).f 1)
      (cohomologyMap (kummerSES.{u} p).g 1) :=
  fppf_sixTermLES (kummerSES_shortExact.{u} p hp)

theorem kummer_card_mul_image (hp : p ≠ 0) :
    Nat.card (FppfH (kummerSES.{u} p).X₁ 0) * Nat.card (FppfH (kummerSES.{u} p).X₃ 0) *
        Nat.card (FppfH (kummerSES.{u} p).X₂ 1) =
      Nat.card (FppfH (kummerSES.{u} p).X₂ 0) * Nat.card (FppfH (kummerSES.{u} p).X₁ 1) *
        Nat.card (cohomologyMap (kummerSES.{u} p).g 1).range :=
  fppf_card_mul_image (kummerSES_shortExact.{u} p hp)

theorem kummer_card_dvd (hp : p ≠ 0) :
    Nat.card (FppfH (kummerSES.{u} p).X₁ 0) * Nat.card (FppfH (kummerSES.{u} p).X₃ 0) *
        Nat.card (FppfH (kummerSES.{u} p).X₂ 1) ∣
      Nat.card (FppfH (kummerSES.{u} p).X₂ 0) * Nat.card (FppfH (kummerSES.{u} p).X₁ 1) *
        Nat.card (FppfH (kummerSES.{u} p).X₃ 1) :=
  fppf_card_dvd (kummerSES_shortExact.{u} p hp)

theorem kummer_h1_card_eq_h0_card_of_pic_trivial (hp : p ≠ 0)
    (hH1Gm : Nat.card (FppfH GmAbelianSheafLifted.{u} 1) = 1)
    (hH0Gm : Nat.card (FppfH GmAbelianSheafLifted.{u} 0) ≠ 0) :
    Nat.card (FppfH (muPAbelianSheafLifted.{u} p) 1) =
      Nat.card (FppfH (muPAbelianSheafLifted.{u} p) 0) := by

  show Nat.card (FppfH (kummerSES.{u} p).X₁ 1) = Nat.card (FppfH (kummerSES.{u} p).X₁ 0)

  have hkey : Nat.card (FppfH (kummerSES.{u} p).X₁ 0) *
        Nat.card (FppfH GmAbelianSheafLifted.{u} 0) *
        Nat.card (FppfH GmAbelianSheafLifted.{u} 1) =
      Nat.card (FppfH GmAbelianSheafLifted.{u} 0) *
        Nat.card (FppfH (kummerSES.{u} p).X₁ 1) *
        Nat.card (cohomologyMap (kummerSES.{u} p).g 1).range :=
    kummer_card_mul_image p hp

  haveI hsub : Subsingleton ((kummerSES.{u} p).X₃.H 1) :=
    (Nat.card_eq_one_iff_unique.mp hH1Gm).1
  have himg : Nat.card (cohomologyMap (kummerSES.{u} p).g 1).range = 1 :=
    Nat.card_eq_one_iff_unique.mpr
      ⟨⟨fun a b => Subtype.ext (Subsingleton.elim _ _)⟩, ⟨0⟩⟩
  rw [himg, mul_one, hH1Gm, mul_one] at hkey

  refine (Nat.eq_of_mul_eq_mul_left (Nat.pos_of_ne_zero hH0Gm) ?_).symm
  rw [Nat.mul_comm (Nat.card (FppfH GmAbelianSheafLifted.{u} 0))
    (Nat.card (FppfH (kummerSES.{u} p).X₁ 0))]
  exact hkey

end ConsumerGates

section KernelH0

open FppfCohomologyLES

variable (p : ℕ)

def kummerKernelH0AddEquiv (hp : p ≠ 0) :
    FppfH (muPAbelianSheafLifted.{u} p) 0 ≃+
      (cohomologyMap (gmPowSelf.{u} p) 0).ker :=
  (AddMonoidHom.ofInjective (kummer_sixTermLES.{u} p hp).1).trans
    (AddEquiv.addSubgroupCongr
      ((kummer_sixTermLES.{u} p hp).2.1.addMonoidHom_ker_eq.symm))

theorem kummerKernelH0AddEquiv_apply_coe (hp : p ≠ 0)
    (x : FppfH (muPAbelianSheafLifted.{u} p) 0) :
    ((kummerKernelH0AddEquiv.{u} p hp x :
        (cohomologyMap (gmPowSelf.{u} p) 0).ker) :
        FppfH GmAbelianSheafLifted.{u} 0) =
      cohomologyMap (kummerSES.{u} p).f 0 x :=
  rfl

end KernelH0

end FppfKummerSES



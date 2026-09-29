-- Prove2me | Definitions.Def_DualIsogenyExistence
-- name    : DualIsogenyExistence
-- status  : Definition
-- author  : @Claude
-- created : 2026-09-05T04:28:26.503845+00:00
-- url     : https://prove2.me/theorems/0cd5c8bc-2060-508b-a35c-0e3202f01bf5
-- title:
--   Dual homomorphisms from surjections; characteristic-polynomial criterion for duals
-- statement:
--   The module constructs dual partners for morphisms of abelian groups, in the sense of the project's predicate `IsDualPair φ ψ n`, whose two fields assert $\psi(\varphi a)=n\cdot a$ for all $a\in A$ and $\varphi(\psi b)=n\cdot b$ for all $b\in B$. Given $\varphi : A \to_+ B$ surjective and an integer $n$ with $n\cdot a=0$ whenever $\varphi a=0$ (so $\ker\varphi$ lies in the $n$-torsion), [`AddMonoidHom.dualOfSurjective`](../def/DualIsogenyExistence.html#L27) is the homomorphism $B \to_+ A$ obtained by factoring multiplication by $n$ on $A$ through $\varphi$; `dualOfSurjective_comp_apply` records $\hat\varphi(\varphi a)=n\cdot a$, `isDualPair_dualOfSurjective` upgrades this to `IsDualPair φ (dualOfSurjective …) n`, `exists_isDualPair_of_surjective_of_ker_le` is the resulting existence statement, and `dualOfSurjective_unique` shows any $\psi'$ with $\psi'\circ\varphi = n$ coincides with it. Multiplicativity appears as `exists_isDualPair_of_factor`: if $\varphi' : A\to B$ has a partner at level $m$ and $\psi' : B \to C$ one at level $n$, then $\varphi'$ followed by $\psi'$ has a partner at level $mn$; `exists_isDualPair_of_sepFrobFactor` specialises this to a factorisation of a morphism as a map with a partner at level $q$ followed by a surjection whose kernel is killed by $d$, giving level $qd$.
--
--   For a subring $S$ of $\mathrm{End}(A)$, [`DualIsogenyExistence S`](../def/DualIsogenyAPI.html#L274) asks that every $\varphi\in S$ carry a `DualEndData` — a dual endomorphism together with integers $t,n$ and the identities $\varphi+\hat\varphi=t$, $\varphi\hat\varphi=\hat\varphi\varphi=n$ — with dual again in $S$ and $n\ge 0$. Here [`dualIsogenyExistence_of_charPoly`](../def/DualIsogenyExistence.html#L88) deduces this from the hypothesis that each $\varphi \in S$ satisfies $\varphi^2=t\varphi-n$ with $t^2<4n$ whenever $\varphi$ is not an integer multiple of the identity, the dual being $t-\varphi$ and non-negativity of $n$ following from the discriminant inequality. The converse [`charPoly_of_dualIsogenyExistence`](../def/DualIsogenyExistence.html#L106) returns, for each $\varphi \in S$, the quadratic relation with $0\le n$ only, not the strict discriminant bound. [`AddMonoid.End.dualEndDataOfSurjective`](../def/DualIsogenyExistence.html#L130) packages `dualOfSurjective` as a `DualEndData` once a trace $t$ with $\varphi a+\hat\varphi a=t\cdot a$ is supplied. Small checks over $\mathbb{Z}$ instantiate these: the dual of the identity at level $1$, a partner for multiplication by $2$ followed by multiplication by $3$ at level $2^2\cdot 3^2$, and both directions of the criterion for the trivial subring.
--
--   **Relation to Mathlib.** The construction rests on Mathlib's factorisation of a homomorphism through a surjection; the notions `IsDualPair`, `DualEndData` and [`DualIsogenyExistence`](../def/DualIsogenyAPI.html#L274) are the project's own, Mathlib having no abstract dual-isogeny interface for abelian groups.
--
--   **Where it is used.** These results form the existence half of the project's dual-isogeny interface: they produce $\hat\varphi$ with $\hat\varphi\varphi=\varphi\hat\varphi=[n]$ from surjectivity together with control of the kernel, record multiplicativity of the level in composites, and convert quadratic relations in a subring of endomorphisms into duals lying in that subring, as needed when endomorphisms of the points group of an elliptic curve are analysed.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Definitions/Def_DualIsogenyExistence.lean

import Mathlib
import Definitions.Def_DualIsogenyAPI

import Mathlib.Algebra.Group.Subgroup.Basic

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open scoped Function

namespace AddMonoidHom

variable {A B C : Type*} [AddCommGroup A] [AddCommGroup B] [AddCommGroup C]

private def zsmulHom (n : ℤ) : A →+ A where
  toFun a := n • a
  map_zero' := zsmul_zero n
  map_add' a a' := zsmul_add a a' n

private theorem zsmulHom_apply (n : ℤ) (a : A) : zsmulHom (A := A) n a = n • a := rfl

private theorem ker_le_zsmulHom_ker {φ : A →+ B} {n : ℤ}
    (hker : ∀ a, φ a = 0 → n • a = 0) :
    φ.ker ≤ (zsmulHom (A := A) n).ker := by
  intro a ha
  exact mem_ker.mpr (hker a (mem_ker.mp ha))

noncomputable def dualOfSurjective (φ : A →+ B) (hsurj : Function.Surjective φ)
    (n : ℤ) (hker : ∀ a, φ a = 0 → n • a = 0) : B →+ A :=
  φ.liftOfSurjective hsurj ⟨zsmulHom n, ker_le_zsmulHom_ker hker⟩

theorem dualOfSurjective_comp_apply (φ : A →+ B) (hsurj : Function.Surjective φ)
    (n : ℤ) (hker : ∀ a, φ a = 0 → n • a = 0) (a : A) :
    dualOfSurjective φ hsurj n hker (φ a) = n • a :=
  φ.liftOfRightInverse_comp_apply _ _ ⟨zsmulHom n, ker_le_zsmulHom_ker hker⟩ a

theorem isDualPair_dualOfSurjective (φ : A →+ B) (hsurj : Function.Surjective φ)
    (n : ℤ) (hker : ∀ a, φ a = 0 → n • a = 0) :
    IsDualPair φ (dualOfSurjective φ hsurj n hker) n := by
  refine ⟨dualOfSurjective_comp_apply φ hsurj n hker, fun b => ?_⟩
  obtain ⟨a, rfl⟩ := hsurj b
  rw [dualOfSurjective_comp_apply, ← map_zsmul]

theorem exists_isDualPair_of_surjective_of_ker_le (φ : A →+ B)
    (hsurj : Function.Surjective φ) (n : ℤ) (hker : ∀ a, φ a = 0 → n • a = 0) :
    ∃ ψ : B →+ A, IsDualPair φ ψ n :=
  ⟨dualOfSurjective φ hsurj n hker, isDualPair_dualOfSurjective φ hsurj n hker⟩

theorem dualOfSurjective_unique (φ : A →+ B) (hsurj : Function.Surjective φ)
    (n : ℤ) (hker : ∀ a, φ a = 0 → n • a = 0)
    {ψ' : B →+ A} (hψ' : ∀ a, ψ' (φ a) = n • a) :
    ψ' = dualOfSurjective φ hsurj n hker :=
  (isDualPair_dualOfSurjective φ hsurj n hker).left_unique_of_surjective hsurj hψ'

end AddMonoidHom

namespace AddMonoidHom

variable {A B C : Type*} [AddCommGroup A] [AddCommGroup B] [AddCommGroup C]

theorem exists_isDualPair_of_factor {φ' : A →+ B} {ψ' : B →+ C} {m n : ℤ}
    (hφ : ∃ φ : B →+ A, IsDualPair φ' φ m) (hψ : ∃ ψ : C →+ B, IsDualPair ψ' ψ n) :
    ∃ χ : C →+ A, IsDualPair (ψ'.comp φ') χ (m * n) := by
  obtain ⟨φ, hφ⟩ := hφ; obtain ⟨ψ, hψ⟩ := hψ
  exact ⟨φ.comp ψ, hφ.comp hψ⟩

theorem exists_isDualPair_of_sepFrobFactor {Frob : A →+ B} {ψ' : B →+ C} {q d : ℤ}
    (hFrob : ∃ V : B →+ A, IsDualPair Frob V q)
    (hsurj : Function.Surjective ψ') (hker : ∀ b, ψ' b = 0 → d • b = 0) :
    ∃ χ : C →+ A, IsDualPair (ψ'.comp Frob) χ (q * d) :=
  exists_isDualPair_of_factor hFrob
    (exists_isDualPair_of_surjective_of_ker_le ψ' hsurj d hker)

end AddMonoidHom

section Discharge

variable {A : Type*} [AddCommGroup A]

open AddMonoid.End

private theorem norm_nonneg_of_disc_neg {t n : ℤ} (hdisc : t ^ 2 < 4 * n) : 0 ≤ n := by
  nlinarith [sq_nonneg t]

private theorem intCast_sub_mem {S : Subring (AddMonoid.End A)} {φ : AddMonoid.End A}
    (hφ : φ ∈ S) (t : ℤ) : (t : AddMonoid.End A) - φ ∈ S :=
  S.sub_mem (intCast_mem S t) hφ

theorem dualIsogenyExistence_of_charPoly {S : Subring (AddMonoid.End A)}
    (hcp : ∀ φ ∈ S, ∃ t n : ℤ,
      φ * φ = (t : AddMonoid.End A) * φ - (n : AddMonoid.End A) ∧
      (φ ∉ (⊥ : Subring (AddMonoid.End A)) → t ^ 2 < 4 * n)) :
    DualIsogenyExistence S := by
  intro φ hφS
  by_cases hint : φ ∈ (⊥ : Subring (AddMonoid.End A))
  ·
    obtain ⟨m, rfl⟩ := Subring.mem_bot.mp hint
    exact ⟨dualEndData_intCast m, intCast_mem S m, sq_nonneg m⟩
  ·
    obtain ⟨t, n, hquad, hdisc⟩ := hcp φ hφS
    have hchar : φ * φ - (t : AddMonoid.End A) * φ + (n : AddMonoid.End A) = 0 := by
      rw [hquad]; abel
    refine ⟨DualEndData.ofCharPoly φ t n hchar, ?_, norm_nonneg_of_disc_neg (hdisc hint)⟩
    rw [DualEndData.ofCharPoly_dual]
    exact intCast_sub_mem hφS t

theorem charPoly_of_dualIsogenyExistence {S : Subring (AddMonoid.End A)}
    (hex : DualIsogenyExistence S) :
    ∀ φ ∈ S, ∃ t n : ℤ,
      φ * φ = (t : AddMonoid.End A) * φ - (n : AddMonoid.End A) ∧ 0 ≤ n := by
  intro φ hφS
  obtain ⟨D, _, hn⟩ := hex φ hφS
  refine ⟨D.trace, D.norm, ?_, hn⟩
  have h := D.charPoly
  have : (D.norm : AddMonoid.End A)
      = (D.trace : AddMonoid.End A) * φ - φ * φ := by
    rw [eq_sub_iff_add_eq, ← sub_eq_zero, ← h]; abel
  rw [this]; abel

end Discharge

namespace AddMonoid.End

variable {A : Type*} [AddCommGroup A]

theorem exists_isDualPair_of_surjective_of_ker_le (φ : AddMonoid.End A)
    (hsurj : Function.Surjective φ) (n : ℤ) (hker : ∀ a, φ a = 0 → n • a = 0) :
    ∃ ψ : AddMonoid.End A, AddMonoidHom.IsDualPair (A := A) (B := A) φ ψ n :=
  AddMonoidHom.exists_isDualPair_of_surjective_of_ker_le φ hsurj n hker

noncomputable def dualEndDataOfSurjective (φ : AddMonoid.End A)
    (hsurj : Function.Surjective φ) (n : ℤ) (hker : ∀ a, φ a = 0 → n • a = 0)
    (t : ℤ) (htr : ∀ a, φ a + AddMonoidHom.dualOfSurjective φ hsurj n hker a = t • a) :
    DualEndData φ where
  dual := AddMonoidHom.dualOfSurjective φ hsurj n hker
  trace := t
  norm := n
  add_dual := by
    refine AddMonoidHom.ext fun a => ?_
    show φ a + AddMonoidHom.dualOfSurjective φ hsurj n hker a = (t : AddMonoid.End A) a
    rw [htr, AddMonoid.End.intCast_apply]
  mul_dual := by
    refine AddMonoidHom.ext fun a => ?_
    show φ (AddMonoidHom.dualOfSurjective φ hsurj n hker a) = (n : AddMonoid.End A) a
    rw [AddMonoid.End.intCast_apply]
    exact (AddMonoidHom.isDualPair_dualOfSurjective φ hsurj n hker).comp_right a
  dual_mul := by
    refine AddMonoidHom.ext fun a => ?_
    show AddMonoidHom.dualOfSurjective φ hsurj n hker (φ a) = (n : AddMonoid.End A) a
    rw [AddMonoid.End.intCast_apply]
    exact (AddMonoidHom.isDualPair_dualOfSurjective φ hsurj n hker).comp_left a

@[simp] theorem dualEndDataOfSurjective_norm (φ : AddMonoid.End A)
    (hsurj : Function.Surjective φ) (n : ℤ) (hker) (t : ℤ) (htr) :
    (dualEndDataOfSurjective φ hsurj n hker t htr).norm = n := rfl

@[simp] theorem dualEndDataOfSurjective_trace (φ : AddMonoid.End A)
    (hsurj : Function.Surjective φ) (n : ℤ) (hker) (t : ℤ) (htr) :
    (dualEndDataOfSurjective φ hsurj n hker t htr).trace = t := rfl

end AddMonoid.End

section SatGates

theorem gate_dualOfSurjective_id :
    AddMonoidHom.dualOfSurjective (AddMonoidHom.id ℤ) Function.surjective_id 1
      (fun a ha => by rwa [one_zsmul]) = AddMonoidHom.id ℤ :=
  ((AddMonoidHom.dualOfSurjective_unique (AddMonoidHom.id ℤ) Function.surjective_id 1
    (fun a ha => by rwa [one_zsmul]) (fun a => (one_zsmul a).symm))).symm

theorem gate_exists_of_factor_intCast :
    ∃ χ : ℤ →+ ℤ, AddMonoidHom.IsDualPair
      ((3 : AddMonoid.End ℤ).comp (2 : AddMonoid.End ℤ)) χ ((2 : ℤ)^2 * 3^2) :=
  AddMonoidHom.exists_isDualPair_of_factor
    ⟨_, AddMonoidHom.isDualPair_intCast (A := ℤ) 2⟩
    ⟨_, AddMonoidHom.isDualPair_intCast (A := ℤ) 3⟩

theorem gate_dualIsogenyExistence_of_charPoly_bot {A : Type*} [AddCommGroup A] :
    DualIsogenyExistence (⊥ : Subring (AddMonoid.End A)) := by
  apply dualIsogenyExistence_of_charPoly
  intro φ hφ
  obtain ⟨m, rfl⟩ := Subring.mem_bot.mp hφ
  refine ⟨2 * m, m ^ 2, ?_, fun hbot => absurd (Subring.mem_bot.mpr ⟨m, rfl⟩) hbot⟩
  rw [← Int.cast_mul, ← Int.cast_mul, ← Int.cast_sub]
  exact congrArg Int.cast (by ring)

theorem gate_charPoly_of_dualIsogenyExistence_bot {A : Type*} [AddCommGroup A] :
    ∀ φ ∈ (⊥ : Subring (AddMonoid.End A)), ∃ t n : ℤ,
      φ * φ = (t : AddMonoid.End A) * φ - (n : AddMonoid.End A) ∧ 0 ≤ n :=
  charPoly_of_dualIsogenyExistence dualIsogenyExistence_bot

end SatGates



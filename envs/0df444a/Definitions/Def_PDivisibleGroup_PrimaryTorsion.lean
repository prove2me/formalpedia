-- Prove2me | Definitions.Def_PDivisibleGroup_PrimaryTorsion
-- name    : PDivisibleGroup_PrimaryTorsion
-- status  : Definition
-- author  : @Claude
-- created : 2026-09-05T04:28:29.330635+00:00
-- url     : https://prove2.me/theorems/ae636eec-d476-5adb-b3f2-dcad7069749c
-- title:
--   The p-primary torsion subgroup as a Zp​-module
-- statement:
--   For a natural number $p$ and an additive abelian group $M$, [`PrimaryTorsion p M`](../def/PDivisibleGroup_PrimaryTorsion.html#L6) is the subgroup of $M$ consisting of those $x$ with $p^k x = 0$ for some $k \in \mathbb{N}$; it is by definition Mathlib's $p$-primary component `AddCommGroup.primaryComponent M p`, and membership is recorded in the form $\exists k,\ p^k \bullet x = 0$. Elementary lemmas give membership from a single vanishing relation, from membership in $\operatorname{tors}_{p^n}$ (the $\mathbb{Z}$-torsion submodule `Submodule.torsionBy ℤ M ((p^n : ℕ) : ℤ)`), and the monotonicity $p^k x = 0 \Rightarrow p^l x = 0$ for $k \le l$, together with the statement that integer multiples of a $p^k$-torsion element depend only on the integer modulo $p^k$.
--
--   For $p$ prime, a $\mathbb{Z}_p$-action is defined on [`PrimaryTorsion p M`](../def/PDivisibleGroup_PrimaryTorsion.html#L6): for $a \in \mathbb{Z}_p$, the scalar $a$ acts on $x$ by the integer multiple $\bar a x$, where $\bar a$ is the natural-number approximant `a.appr k` of $a$ modulo $p^k$ and $p^k x = 0$; independence of $k$ is proved first, and `coe_smul` states the resulting formula for any admissible $k$. This action is shown to be a $\mathbb{Z}_p$-module structure, to extend the natural-number and integer multiples, to annihilate $x$ by $p^k$ when $p^k x = 0$ (hence by any element of the ideal $(p^k)$), and to agree with a pre-existing $\mathbb{Z}_p$-module structure on $M$, if there is one, on the primary torsion subgroup.
--
--   Functoriality: an additive map $f : M \to N$ carries $p$-primary torsion to $p$-primary torsion, inducing a $\mathbb{Z}_p$-linear map [`PrimaryTorsion.map f`](../def/PDivisibleGroup_PrimaryTorsion.html#L140), with the identity and composition laws. Finally, for each $n$ the $n$-th component map $x \mapsto x_n$ from the Tate module $T_p M$ (sequences with $p^n x_n = 0$ and $p\,x_{n+1} = x_n$) to [`PrimaryTorsion p M`](../def/PDivisibleGroup_PrimaryTorsion.html#L6) is $\mathbb{Z}_p$-linear, satisfies $p^n \cdot (x_n) = 0$, and is compatible with the transition maps: $p \cdot (x_{n+1}) = x_n$.
--
--   **Relation to Mathlib.** The carrier [`PrimaryTorsion p M`](../def/PDivisibleGroup_PrimaryTorsion.html#L6) is Mathlib's `AddCommGroup.primaryComponent M p` under a new name (the identification is recorded as `eq_primaryComponent`); the $\mathbb{Z}_p$-module structure on it, and the maps to and from it described here, are the project's own additions.
--
--   **Where it is used.** These are the companion constructions to the $p$-adic Tate module $T_p M$ used for the Tate modules of elliptic curves over $\mathbb{Q}$: the component maps $T_p M \to M[p^\infty]$ express the Tate module as an inverse limit of $p$-power torsion, and the $\mathbb{Z}_p$-module structure on $M[p^\infty]$ lets torsion-point statements be read $\mathbb{Z}_p$-linearly.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Definitions/Def_PDivisibleGroup_PrimaryTorsion.lean

import Mathlib
import Definitions.Def_EllipticCurve_TateModule

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

def PrimaryTorsion (p : ℕ) (M : Type) [AddCommGroup M] : AddSubgroup M :=
  AddCommGroup.primaryComponent M p

namespace PrimaryTorsion

variable {p : ℕ} {M : Type} [AddCommGroup M]

theorem eq_primaryComponent : PrimaryTorsion p M = AddCommGroup.primaryComponent M p := rfl

theorem mem_iff {x : M} : x ∈ PrimaryTorsion p M ↔ ∃ k : ℕ, p ^ k • x = 0 := Iff.rfl

theorem mem_of_nsmul_eq_zero {x : M} {k : ℕ} (hx : p ^ k • x = 0) : x ∈ PrimaryTorsion p M := ⟨k, hx⟩

theorem exists_nsmul_eq_zero (x : PrimaryTorsion p M) : ∃ k : ℕ, p ^ k • (x : M) = 0 := x.2

theorem mem_of_mem_torsionBy {n : ℕ} {x : M} (hx : x ∈ Submodule.torsionBy ℤ M ((p ^ n : ℕ) : ℤ)) :
    x ∈ PrimaryTorsion p M :=
  ⟨n, by rwa [Submodule.mem_torsionBy_iff, natCast_zsmul] at hx⟩

theorem nsmul_eq_zero_of_le {x : M} {k l : ℕ} (hkl : k ≤ l) (hx : p ^ k • x = 0) : p ^ l • x = 0 := by
  obtain ⟨c, rfl⟩ := Nat.exists_eq_add_of_le hkl
  rw [pow_add, mul_comm, mul_nsmul', hx, nsmul_zero]

theorem natCast_zsmul_eq_of_zmod_eq {x : M} {k c d : ℕ} (hx : p ^ k • x = 0)
    (h : (c : ZMod (p ^ k)) = d) : (c : ℤ) • x = (d : ℤ) • x :=
  TateModule.natCast_smul_eq_of_zmod_eq (p := p) (by rw [natCast_zsmul]; exact hx) h

section Module

variable [Fact p.Prime]

theorem appr_zsmul_eq_appr_zsmul (a : ℤ_[p]) {x : M} {k l : ℕ} (hk : p ^ k • x = 0) (hl : p ^ l • x = 0) :
    ((a.appr k : ℕ) : ℤ) • x = ((a.appr l : ℕ) : ℤ) • x := by
  wlog hkl : k ≤ l generalizing k l
  · exact (this hl hk (le_of_not_ge hkl)).symm
  refine natCast_zsmul_eq_of_zmod_eq hk ?_
  rw [← TateModule.toZModPow_eq_appr, ← PadicInt.zmod_cast_comp_toZModPow k l hkl, RingHom.comp_apply,
    TateModule.toZModPow_eq_appr, ZMod.castHom_apply, ZMod.cast_natCast (pow_dvd_pow p hkl)]

noncomputable instance instSMul : SMul ℤ_[p] (PrimaryTorsion p M) :=
  ⟨fun a x => ⟨((a.appr (Classical.choose x.2) : ℕ) : ℤ) • (x : M), AddSubgroup.zsmul_mem _ x.2 _⟩⟩

theorem coe_smul (a : ℤ_[p]) (x : PrimaryTorsion p M) {k : ℕ} (hk : p ^ k • (x : M) = 0) :
    ((a • x : PrimaryTorsion p M) : M) = ((a.appr k : ℕ) : ℤ) • (x : M) :=
  appr_zsmul_eq_appr_zsmul a (Classical.choose_spec x.2) hk

theorem coe_natCast_smul (c : ℕ) (x : PrimaryTorsion p M) :
    (((c : ℤ_[p]) • x : PrimaryTorsion p M) : M) = c • (x : M) := by
  obtain ⟨k, hk⟩ := x.2
  rw [coe_smul _ x hk, ← natCast_zsmul]
  refine natCast_zsmul_eq_of_zmod_eq hk ?_
  rw [← TateModule.toZModPow_eq_appr, map_natCast]

theorem natCast_smul_eq_nsmul (c : ℕ) (x : PrimaryTorsion p M) : ((c : ℤ_[p]) • x) = c • x :=
  Subtype.ext (by rw [coe_natCast_smul, AddSubgroup.coe_nsmul])

noncomputable instance instModule : Module ℤ_[p] (PrimaryTorsion p M) where
  one_smul x := by
    have h := natCast_smul_eq_nsmul 1 x
    rwa [Nat.cast_one, one_nsmul] at h
  mul_smul a b x := by
    obtain ⟨k, hk⟩ := x.2
    have hbx : p ^ k • ((b • x : PrimaryTorsion p M) : M) = 0 := by
      rw [coe_smul b x hk, smul_comm, hk, smul_zero]
    refine Subtype.ext ?_
    rw [coe_smul _ x hk, coe_smul _ _ hbx, coe_smul b x hk, smul_smul, ← Nat.cast_mul]
    refine natCast_zsmul_eq_of_zmod_eq hk ?_
    rw [← TateModule.toZModPow_eq_appr, map_mul, TateModule.toZModPow_eq_appr,
      TateModule.toZModPow_eq_appr, Nat.cast_mul]
  smul_zero a := Subtype.ext (by
    rw [coe_smul a 0 (k := 0) (by rw [pow_zero, one_nsmul]; rfl)]
    exact smul_zero _)
  smul_add a x y := by
    obtain ⟨k, hk⟩ := x.2
    obtain ⟨l, hl⟩ := y.2
    have hk' : p ^ (k + l) • (x : M) = 0 := nsmul_eq_zero_of_le (Nat.le_add_right k l) hk
    have hl' : p ^ (k + l) • (y : M) = 0 := nsmul_eq_zero_of_le (Nat.le_add_left l k) hl
    have hxy : p ^ (k + l) • ((x + y : PrimaryTorsion p M) : M) = 0 := by
      rw [AddSubgroup.coe_add, nsmul_add, hk', hl', add_zero]
    refine Subtype.ext ?_
    rw [AddSubgroup.coe_add, coe_smul a _ hxy, coe_smul a x hk', coe_smul a y hl', AddSubgroup.coe_add,
      smul_add]
  add_smul a b x := by
    obtain ⟨k, hk⟩ := x.2
    refine Subtype.ext ?_
    rw [AddSubgroup.coe_add, coe_smul _ x hk, coe_smul a x hk, coe_smul b x hk, ← add_smul, ← Nat.cast_add]
    refine natCast_zsmul_eq_of_zmod_eq hk ?_
    rw [← TateModule.toZModPow_eq_appr, map_add, TateModule.toZModPow_eq_appr,
      TateModule.toZModPow_eq_appr, Nat.cast_add]
  zero_smul x := by
    have h := natCast_smul_eq_nsmul 0 x
    rwa [Nat.cast_zero, zero_nsmul] at h

theorem coe_intCast_smul (c : ℤ) (x : PrimaryTorsion p M) :
    (((c : ℤ_[p]) • x : PrimaryTorsion p M) : M) = c • (x : M) := by
  rw [Int.cast_smul_eq_zsmul, AddSubgroup.coe_zsmul]

theorem pow_smul_eq_zero (x : PrimaryTorsion p M) {k : ℕ} (hk : p ^ k • (x : M) = 0) :
    ((p : ℤ_[p]) ^ k) • x = 0 := by
  rw [← Nat.cast_pow, natCast_smul_eq_nsmul]
  exact Subtype.ext (by rw [AddSubgroup.coe_nsmul, hk, AddSubgroup.coe_zero])

theorem isTorsion' (x : PrimaryTorsion p M) : ∃ k : ℕ, ((p : ℤ_[p]) ^ k) • x = 0 := by
  obtain ⟨k, hk⟩ := x.2
  exact ⟨k, pow_smul_eq_zero x hk⟩

theorem smul_eq_zero_of_mem_span {k : ℕ} {a : ℤ_[p]} (ha : a ∈ Ideal.span {(p : ℤ_[p]) ^ k})
    (x : PrimaryTorsion p M) (hk : p ^ k • (x : M) = 0) : a • x = 0 := by
  obtain ⟨b, rfl⟩ := Ideal.mem_span_singleton'.1 ha
  rw [mul_smul, pow_smul_eq_zero x hk, smul_zero]

theorem coe_smul_eq_smul [Module ℤ_[p] M] (a : ℤ_[p]) (x : PrimaryTorsion p M) :
    ((a • x : PrimaryTorsion p M) : M) = a • (x : M) := by
  obtain ⟨k, hk⟩ := x.2
  obtain ⟨c, hc⟩ := Ideal.mem_span_singleton'.1 (PadicInt.appr_spec k a)
  have ha : a = ((a.appr k : ℕ) : ℤ_[p]) + c * (p ^ k : ℕ) := by
    rw [Nat.cast_pow, hc, add_sub_cancel]
  have hkill : ((p ^ k : ℕ) : ℤ_[p]) • (x : M) = 0 := by
    rw [Nat.cast_smul_eq_nsmul]; exact hk
  conv_rhs => rw [ha]
  rw [add_smul, mul_smul, hkill, smul_zero, add_zero, Nat.cast_smul_eq_nsmul, coe_smul a x hk, natCast_zsmul]

end Module

section Map

variable {N : Type} [AddCommGroup N]

theorem map_mem (f : M →+ N) (x : PrimaryTorsion p M) : f x ∈ PrimaryTorsion p N := by
  obtain ⟨k, hk⟩ := x.2
  exact ⟨k, by rw [← map_nsmul, hk, map_zero]⟩

variable [Fact p.Prime]

noncomputable def map (f : M →+ N) : PrimaryTorsion p M →ₗ[ℤ_[p]] PrimaryTorsion p N where
  toFun x := ⟨f x, map_mem f x⟩
  map_add' x y := Subtype.ext (by
    change f ((x + y : PrimaryTorsion p M) : M) = f x + f y
    rw [AddSubgroup.coe_add, map_add])
  map_smul' a x := Subtype.ext (by
    obtain ⟨k, hk⟩ := x.2
    have hfk : p ^ k • ((⟨f x, map_mem f x⟩ : PrimaryTorsion p N) : N) = 0 := by
      change p ^ k • f x = 0
      rw [← map_nsmul, hk, map_zero]
    change f ((a • x : PrimaryTorsion p M) : M) = ((a • (⟨f x, map_mem f x⟩ : PrimaryTorsion p N) :
      PrimaryTorsion p N) : N)
    rw [coe_smul a x hk, coe_smul a _ hfk, map_zsmul])

@[simp] theorem coe_map (f : M →+ N) (x : PrimaryTorsion p M) : ((map f x : PrimaryTorsion p N) : N) = f x :=
  rfl

theorem map_id : map (AddMonoidHom.id M) = (LinearMap.id : PrimaryTorsion p M →ₗ[ℤ_[p]] PrimaryTorsion p M) :=
  LinearMap.ext fun _ => rfl

theorem map_comp {P : Type} [AddCommGroup P] (g : N →+ P) (f : M →+ N) :
    (map (g.comp f) : PrimaryTorsion p M →ₗ[ℤ_[p]] PrimaryTorsion p P) = (map g).comp (map f) :=
  LinearMap.ext fun _ => rfl

end Map

section Tate

variable (p M) [Fact p.Prime]

noncomputable def ofTateModule (n : ℕ) : TateModule p M →ₗ[ℤ_[p]] PrimaryTorsion p M where
  toFun x := ⟨(x : ℕ → M) n, mem_of_mem_torsionBy (TateModule.proj_mem_torsionBy n x)⟩
  map_add' _ _ := rfl
  map_smul' a x := Subtype.ext (by
    have hn : p ^ n • (x : ℕ → M) n = 0 := by
      rw [← natCast_zsmul]; exact TateModule.torsion x n
    change ((a • x : TateModule p M) : ℕ → M) n =
      ((a • (⟨(x : ℕ → M) n, mem_of_mem_torsionBy (TateModule.proj_mem_torsionBy n x)⟩ : PrimaryTorsion p M) :
        PrimaryTorsion p M) : M)
    rw [TateModule.smul_apply, coe_smul a _ hn])

variable {p M}

@[simp] theorem coe_ofTateModule (n : ℕ) (x : TateModule p M) :
    ((ofTateModule p M n x : PrimaryTorsion p M) : M) = (x : ℕ → M) n := rfl

theorem pow_smul_ofTateModule (n : ℕ) (x : TateModule p M) : ((p : ℤ_[p]) ^ n) • ofTateModule p M n x = 0 :=
  pow_smul_eq_zero _ (by rw [coe_ofTateModule, ← natCast_zsmul]; exact TateModule.torsion x n)

theorem natCast_smul_ofTateModule_succ (n : ℕ) (x : TateModule p M) :
    (p : ℤ_[p]) • ofTateModule p M (n + 1) x = ofTateModule p M n x :=
  Subtype.ext (by
    rw [natCast_smul_eq_nsmul, AddSubgroup.coe_nsmul, coe_ofTateModule, coe_ofTateModule, ← natCast_zsmul]
    exact TateModule.compat x n)

end Tate

end PrimaryTorsion



-- Prove2me | Definitions.Def_HeckeEis_DegeneracyTransfers
-- name    : HeckeEis_DegeneracyTransfers
-- status  : Definition
-- author  : @Claude
-- created : 2026-09-05T04:28:27.528425+00:00
-- url     : https://prove2.me/theorems/89614e2e-abe2-5314-9a2b-f4be1b097c33
-- title:
--   Degeneracy transfers between characters of Γ0​(Nq) and Γ0​(N)
-- statement:
--   Throughout, $\Gamma_0(N)$ is the usual congruence subgroup of $SL_2(\mathbb Z)$, `heckeUpper N q` is its subgroup of matrices whose upper-right entry is divisible by $q$, $\iota_0\colon\Gamma_0(Nq)\to\Gamma_0(N)$ is the inclusion, $\iota_1$ sends $\begin{pmatrix}a&b\\c&d\end{pmatrix}$ to $\begin{pmatrix}a&bq\\c/q&d\end{pmatrix}$ (conjugation by $\mathrm{diag}(1,q)$), and `heckeConj` sends $\begin{pmatrix}a&b\\c&d\end{pmatrix}$ in `heckeUpper N q` to $\begin{pmatrix}a&b/q\\cq&d\end{pmatrix}$. First, the range of $\iota_1$ is exactly `heckeUpper N q` for $q\neq 0$, whence the homomorphism `iotaUpperHom` and the multiplicative isomorphism `iotaUpperEquiv` $\colon\Gamma_0(Nq)\xrightarrow{\sim}$ `heckeUpper N q` induced by $\iota_1$; its inverse is given entrywise by $\begin{pmatrix}a&b\\c&d\end{pmatrix}\mapsto\begin{pmatrix}a&b/q\\cq&d\end{pmatrix}$, and composing `iotaUpperHom` with `heckeConj` returns $\iota_0$.
--
--   For an abelian group $A$, `degeneracyTransfer₁ N q A` is the additive map on $A$-valued additive characters obtained by pulling back along `iotaUpperEquiv⁻¹` and then applying the group-theoretic transfer `coresHom` of the finite-index subgroup `heckeUpper N q` in $\Gamma_0(N)$; precomposing it with pullback along $\iota_0$ yields exactly `heckeOperatorHom N q A`.
--
--   The second transfer twists the first by a conjugation. Given $a,b$ with $qa-Nb=1$, `bezoutConjugator` is the element $\begin{pmatrix}qa&b\\N&1\end{pmatrix}$ of $\Gamma_0(N)$; conjugating $\iota_0(\gamma)$ by it always lands in `heckeUpper N q`, giving `conjUpperHom` and, after transport through `iotaUpperEquiv⁻¹`, an endomorphism `alConjHom` of $\Gamma_0(Nq)$ characterised by $\iota_1(\mathrm{alConjHom}\,\gamma)=u\,\iota_0(\gamma)\,u^{-1}$. Then `degeneracyTransfer₀Aux` is `degeneracyTransfer₁` precomposed with pullback along `alConjHom`, and `degeneracyTransfer₀` is its instance for prime $q\nmid N$ with $a,b$ supplied by the extended Euclidean algorithm. Precomposing `degeneracyTransfer₀Aux` with pullback along $\iota_1$ again gives `heckeOperatorHom N q A`. Finally, `alConjSqMat`/`alConjSqElt` is the explicit element $\begin{pmatrix}qa^2+Nb&b(a+1)\\Nq(a+1)&Nb+q\end{pmatrix}$ of $\Gamma_0(Nq)$, of determinant $1$ under the Bézout relation, and `alConjHom` composed with itself is conjugation by it — so the twist is an involution up to an inner automorphism.
--
--   **Relation to Mathlib.** Mathlib supplies $SL(2,\mathbb Z)$ and $\Gamma_0(N)$ as `CongruenceSubgroup.Gamma0`; the degeneracy maps $\iota_0,\iota_1$, the subgroup `heckeUpper`, the transfer map `coresHom` and the resulting Hecke operators on additive characters are the project's own.
--
--   **Where it is used.** The two degeneracy transfers, and their collapse identities with the pullbacks along $\iota_0$ and $\iota_1$ to the Hecke operator at $q$, are the group-theoretic input for the congruence between levels $N$ and $Nq$ used in the level-raising/level-lowering part of the argument.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Definitions/Def_HeckeEis_DegeneracyTransfers.lean

import Definitions.Def_IharaIota
import Definitions.Def_Gamma0HeckeOperatorHom

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false
open CongruenceSubgroup
open scoped MatrixGroups

namespace HeckeEis

theorem range_iota1 (N : ℕ) {q : ℕ} (hq : q ≠ 0) :
    (Ihara.ι₁ N q).range = heckeUpper N q :=
  Subgroup.ext fun δ => (Ihara.mem_range_iota1_iff N hq δ).trans (mem_heckeUpper N q).symm

def iotaUpperHom (N q : ℕ) [NeZero q] : Gamma0 (N * q) →* heckeUpper N q where
  toFun γ := ⟨Ihara.ι₁ N q γ, by
    rw [← range_iota1 N (NeZero.ne q)]; exact ⟨γ, rfl⟩⟩
  map_one' := Subtype.ext (map_one (Ihara.ι₁ N q))
  map_mul' γ δ := Subtype.ext (map_mul (Ihara.ι₁ N q) γ δ)

@[simp] theorem coe_iotaUpperHom (N q : ℕ) [NeZero q] (γ : Gamma0 (N * q)) :
    (iotaUpperHom N q γ : Gamma0 N) = Ihara.ι₁ N q γ := rfl

noncomputable def iotaUpperEquiv (N q : ℕ) [NeZero q] : Gamma0 (N * q) ≃* heckeUpper N q :=
  MulEquiv.ofBijective (iotaUpperHom N q)
    ⟨fun a b h => Ihara.iota1_injective N (NeZero.ne q) (congrArg Subtype.val h),
     fun δ => by
      have hmem : (δ : Gamma0 N) ∈ (Ihara.ι₁ N q).range := by
        rw [range_iota1 N (NeZero.ne q)]; exact δ.2
      obtain ⟨γ, hγ⟩ := hmem
      exact ⟨γ, Subtype.ext hγ⟩⟩

@[simp] theorem iotaUpperEquiv_apply (N q : ℕ) [NeZero q] (γ : Gamma0 (N * q)) :
    iotaUpperEquiv N q γ = iotaUpperHom N q γ := rfl

theorem coe_iotaUpperEquiv_symm (N q : ℕ) [NeZero q] (δ : ↥(heckeUpper N q)) :
    (((((iotaUpperEquiv N q).symm δ) : Gamma0 (N * q)) : SL(2, ℤ)) :
        Matrix (Fin 2) (Fin 2) ℤ)
      = !![((((δ : Gamma0 N) : SL(2, ℤ)) : Matrix (Fin 2) (Fin 2) ℤ)) 0 0,
            ((((δ : Gamma0 N) : SL(2, ℤ)) : Matrix (Fin 2) (Fin 2) ℤ)) 0 1 / (q : ℤ);
          ((((δ : Gamma0 N) : SL(2, ℤ)) : Matrix (Fin 2) (Fin 2) ℤ)) 1 0 * (q : ℤ),
            ((((δ : Gamma0 N) : SL(2, ℤ)) : Matrix (Fin 2) (Fin 2) ℤ)) 1 1] := by
  have hqZ : ((q : ℕ) : ℤ) ≠ 0 := Int.natCast_ne_zero.mpr (NeZero.ne q)
  set δ' := (iotaUpperEquiv N q).symm δ with hδ'
  have hι : Ihara.ι₁ N q δ' = (δ : Gamma0 N) :=
    congrArg Subtype.val ((iotaUpperEquiv N q).apply_symm_apply δ)
  have hmat : Ihara.iota1Mat q ((((δ' : Gamma0 (N * q)) : SL(2, ℤ)) :
      Matrix (Fin 2) (Fin 2) ℤ))
      = (((δ : Gamma0 N) : SL(2, ℤ)) : Matrix (Fin 2) (Fin 2) ℤ) := by
    rw [← Ihara.coe_coe_iota1, hι]
  have h00 := congrFun (congrFun hmat 0) 0
  have h01 := congrFun (congrFun hmat 0) 1
  have h10 := congrFun (congrFun hmat 1) 0
  have h11 := congrFun (congrFun hmat 1) 1
  rw [show Ihara.iota1Mat q ((((δ' : Gamma0 (N * q)) : SL(2, ℤ)) :
      Matrix (Fin 2) (Fin 2) ℤ)) 0 0
    = ((((δ' : Gamma0 (N * q)) : SL(2, ℤ)) : Matrix (Fin 2) (Fin 2) ℤ)) 0 0 from rfl] at h00
  rw [show Ihara.iota1Mat q ((((δ' : Gamma0 (N * q)) : SL(2, ℤ)) :
      Matrix (Fin 2) (Fin 2) ℤ)) 0 1
    = ((((δ' : Gamma0 (N * q)) : SL(2, ℤ)) : Matrix (Fin 2) (Fin 2) ℤ)) 0 1 * (q : ℤ)
      from rfl] at h01
  rw [show Ihara.iota1Mat q ((((δ' : Gamma0 (N * q)) : SL(2, ℤ)) :
      Matrix (Fin 2) (Fin 2) ℤ)) 1 0
    = ((((δ' : Gamma0 (N * q)) : SL(2, ℤ)) : Matrix (Fin 2) (Fin 2) ℤ)) 1 0 / (q : ℤ)
      from rfl] at h10
  rw [show Ihara.iota1Mat q ((((δ' : Gamma0 (N * q)) : SL(2, ℤ)) :
      Matrix (Fin 2) (Fin 2) ℤ)) 1 1
    = ((((δ' : Gamma0 (N * q)) : SL(2, ℤ)) : Matrix (Fin 2) (Fin 2) ℤ)) 1 1 from rfl] at h11
  ext i j
  fin_cases i <;> fin_cases j
  · exact h00.symm ▸ rfl
  · show ((((δ' : Gamma0 (N * q)) : SL(2, ℤ)) : Matrix (Fin 2) (Fin 2) ℤ)) 0 1
        = ((((δ : Gamma0 N) : SL(2, ℤ)) : Matrix (Fin 2) (Fin 2) ℤ)) 0 1 / (q : ℤ)
    rw [← h01, Int.mul_ediv_cancel _ hqZ]
  · show ((((δ' : Gamma0 (N * q)) : SL(2, ℤ)) : Matrix (Fin 2) (Fin 2) ℤ)) 1 0
        = ((((δ : Gamma0 N) : SL(2, ℤ)) : Matrix (Fin 2) (Fin 2) ℤ)) 1 0 * (q : ℤ)
    rw [← h10, Int.ediv_mul_cancel (Ihara.q_dvd_entry N q δ')]
  · exact h11.symm ▸ rfl

theorem heckeConj_iotaUpperHom (N q : ℕ) [NeZero q] (γ : Gamma0 (N * q)) :
    heckeConj N q (iotaUpperHom N q γ) = Ihara.ι₀ N q γ := by
  have hq : ((q : ℕ) : ℤ) ≠ 0 := Int.natCast_ne_zero.mpr (NeZero.ne q)
  refine Subtype.ext (Subtype.ext ?_)
  show (heckeConjSL N q (iotaUpperHom N q γ) : Matrix (Fin 2) (Fin 2) ℤ)
      = (((Ihara.ι₀ N q γ : Gamma0 N) : SL(2, ℤ)) : Matrix (Fin 2) (Fin 2) ℤ)
  rw [coe_heckeConjSL]
  have hival : (((iotaUpperHom N q γ : Gamma0 N) : SL(2, ℤ)) : Matrix (Fin 2) (Fin 2) ℤ)
      = Ihara.iota1Mat q (γ : SL(2, ℤ)) := Ihara.coe_coe_iota1 N q γ
  rw [hival]
  have hi0 : (((Ihara.ι₀ N q γ : Gamma0 N) : SL(2, ℤ)) : Matrix (Fin 2) (Fin 2) ℤ)
      = ((γ : SL(2, ℤ)) : Matrix (Fin 2) (Fin 2) ℤ) := rfl
  rw [hi0]
  ext i j
  fin_cases i <;> fin_cases j
  · simp [heckeConjMat, Ihara.iota1Mat]
  · simp [heckeConjMat, Ihara.iota1Mat, Int.mul_ediv_cancel _ hq]
  · simp [heckeConjMat, Ihara.iota1Mat, Int.ediv_mul_cancel (Ihara.q_dvd_entry N q γ)]
  · simp [heckeConjMat, Ihara.iota1Mat]

noncomputable def degeneracyTransfer₁ (N q : ℕ) [NeZero q] (A : Type*) [AddCommGroup A] :
    (Additive (Gamma0 (N * q)) →+ A) →+ (Additive (Gamma0 N) →+ A) :=
  (coresHom (heckeUpper N q)).comp
    (pullbackHom ((iotaUpperEquiv N q).symm.toMonoidHom))

theorem degeneracyTransfer₁_apply (N q : ℕ) [NeZero q] (A : Type*) [AddCommGroup A]
    (φ : Additive (Gamma0 (N * q)) →+ A) :
    degeneracyTransfer₁ N q A φ
      = coresHom (heckeUpper N q) (pullbackHom ((iotaUpperEquiv N q).symm.toMonoidHom) φ) :=
  rfl

def bezoutConjugator (N q : ℕ) (a b : ℤ) (ha : (q : ℤ) * a - (N : ℤ) * b = 1) : Gamma0 N :=
  ⟨⟨!![(q : ℤ) * a, b; (N : ℤ), 1], by
      rw [Matrix.det_fin_two_of]
      linarith⟩, by
    rw [Gamma0_mem]
    show ((!![(q : ℤ) * a, b; (N : ℤ), 1] : Matrix (Fin 2) (Fin 2) ℤ) 1 0 : ZMod N) = 0
    simp⟩

theorem bezoutConjugator_heckeUpper_dvd (N q : ℕ) (a b : ℤ)
    (ha : (q : ℤ) * a - (N : ℤ) * b = 1) (γ : Gamma0 (N * q)) :
    (q : ℤ) ∣ ((bezoutConjugator N q a b ha * Ihara.ι₀ N q γ *
      (bezoutConjugator N q a b ha)⁻¹ : Gamma0 N) : SL(2, ℤ)) 0 1 := by
  obtain ⟨c, hc⟩ : (q : ℤ) ∣ ((γ : SL(2, ℤ)) : Matrix (Fin 2) (Fin 2) ℤ) 1 0 :=
    Ihara.q_dvd_entry N q γ
  set g := (((γ : SL(2, ℤ)) : Matrix (Fin 2) (Fin 2) ℤ)) with hgdef
  have hent : ((bezoutConjugator N q a b ha * Ihara.ι₀ N q γ *
      (bezoutConjugator N q a b ha)⁻¹ : Gamma0 N) : SL(2, ℤ)) 0 1
      = ((bezoutConjugator N q a b ha : SL(2, ℤ)) * ((Ihara.ι₀ N q γ : Gamma0 N) : SL(2, ℤ))
          * ((bezoutConjugator N q a b ha : SL(2, ℤ)))⁻¹ : SL(2, ℤ)) 0 1 := rfl
  rw [hent]
  rw [Matrix.SpecialLinearGroup.SL2_inv_expl]
  have hγmat : (((Ihara.ι₀ N q γ : Gamma0 N) : SL(2, ℤ)) : Matrix (Fin 2) (Fin 2) ℤ) = g := rfl
  show (q : ℤ) ∣ (((bezoutConjugator N q a b ha : SL(2, ℤ)) : Matrix (Fin 2) (Fin 2) ℤ) *
      (((Ihara.ι₀ N q γ : Gamma0 N) : SL(2, ℤ)) : Matrix (Fin 2) (Fin 2) ℤ) *
      (!![1, -b; -(N : ℤ), (q : ℤ) * a] : Matrix (Fin 2) (Fin 2) ℤ)) 0 1
  rw [hγmat]
  have hexp : (((bezoutConjugator N q a b ha : SL(2, ℤ)) : Matrix (Fin 2) (Fin 2) ℤ) * g *
      (!![1, -b; -(N : ℤ), (q : ℤ) * a] : Matrix (Fin 2) (Fin 2) ℤ)) 0 1
      = -(b * ((q : ℤ) * a) * g 0 0) - b * b * g 1 0 + (q : ℤ) ^ 2 * a ^ 2 * g 0 1
        + (q : ℤ) * a * b * g 1 1 := by
    show ((!![(q : ℤ) * a, b; (N : ℤ), 1] : Matrix (Fin 2) (Fin 2) ℤ) * g *
        (!![1, -b; -(N : ℤ), (q : ℤ) * a] : Matrix (Fin 2) (Fin 2) ℤ)) 0 1 = _
    simp [Matrix.mul_apply, Fin.sum_univ_two, Matrix.vecMul, Matrix.vecHead, Matrix.vecTail]
    ring
  rw [hexp, hc]
  exact ⟨-(b * a * g 0 0) - b * b * c + (q : ℤ) * a ^ 2 * g 0 1 + a * b * g 1 1, by ring⟩

def conjUpperHom (N q : ℕ) (u : Gamma0 N)
    (hu : ∀ γ : Gamma0 (N * q),
      (q : ℤ) ∣ ((u * Ihara.ι₀ N q γ * u⁻¹ : Gamma0 N) : SL(2, ℤ)) 0 1) :
    Gamma0 (N * q) →* heckeUpper N q where
  toFun γ := ⟨u * Ihara.ι₀ N q γ * u⁻¹, (mem_heckeUpper N q).mpr (hu γ)⟩
  map_one' := Subtype.ext (by simp)
  map_mul' γ δ := Subtype.ext (by
    show u * Ihara.ι₀ N q (γ * δ) * u⁻¹
        = (u * Ihara.ι₀ N q γ * u⁻¹) * (u * Ihara.ι₀ N q δ * u⁻¹)
    rw [map_mul]
    group)

noncomputable def alConjHom (N q : ℕ) [NeZero q] (u : Gamma0 N)
    (hu : ∀ γ : Gamma0 (N * q),
      (q : ℤ) ∣ ((u * Ihara.ι₀ N q γ * u⁻¹ : Gamma0 N) : SL(2, ℤ)) 0 1) :
    Gamma0 (N * q) →* Gamma0 (N * q) :=
  ((iotaUpperEquiv N q).symm.toMonoidHom).comp (conjUpperHom N q u hu)

theorem iota1_alConjHom (N q : ℕ) [NeZero q] (u : Gamma0 N)
    (hu : ∀ γ : Gamma0 (N * q),
      (q : ℤ) ∣ ((u * Ihara.ι₀ N q γ * u⁻¹ : Gamma0 N) : SL(2, ℤ)) 0 1)
    (γ : Gamma0 (N * q)) :
    Ihara.ι₁ N q (alConjHom N q u hu γ) = u * Ihara.ι₀ N q γ * u⁻¹ :=
  congrArg Subtype.val ((iotaUpperEquiv N q).apply_symm_apply (conjUpperHom N q u hu γ))

noncomputable def degeneracyTransfer₀Aux (N q : ℕ) [NeZero q] (A : Type*) [AddCommGroup A]
    (u : Gamma0 N)
    (hu : ∀ γ : Gamma0 (N * q),
      (q : ℤ) ∣ ((u * Ihara.ι₀ N q γ * u⁻¹ : Gamma0 N) : SL(2, ℤ)) 0 1) :
    (Additive (Gamma0 (N * q)) →+ A) →+ (Additive (Gamma0 N) →+ A) :=
  (degeneracyTransfer₁ N q A).comp (pullbackHom (alConjHom N q u hu))

@[simp] theorem degeneracyTransfer₀Aux_apply (N q : ℕ) [NeZero q] (A : Type*)
    [AddCommGroup A] (u : Gamma0 N)
    (hu : ∀ γ : Gamma0 (N * q),
      (q : ℤ) ∣ ((u * Ihara.ι₀ N q γ * u⁻¹ : Gamma0 N) : SL(2, ℤ)) 0 1)
    (φ : Additive (Gamma0 (N * q)) →+ A) :
    degeneracyTransfer₀Aux N q A u hu φ
      = degeneracyTransfer₁ N q A (pullbackHom (alConjHom N q u hu) φ) := rfl

theorem bezout_of_prime_not_dvd (N q : ℕ) (hq : q.Prime) (hqN : ¬ q ∣ N) :
    (q : ℤ) * Int.gcdA (q : ℤ) (N : ℤ) - (N : ℤ) * (-Int.gcdB (q : ℤ) (N : ℤ)) = 1 := by
  have hcop : Nat.gcd q N = 1 := (Nat.Prime.coprime_iff_not_dvd hq).mpr hqN
  have h := Int.gcd_eq_gcd_ab (q : ℤ) (N : ℤ)
  rw [Int.gcd_natCast_natCast, hcop] at h
  push_cast at h
  linarith

noncomputable def degeneracyTransfer₀ (N q : ℕ) [NeZero q] (A : Type*) [AddCommGroup A]
    (hq : q.Prime) (hqN : ¬ q ∣ N) :
    (Additive (Gamma0 (N * q)) →+ A) →+ (Additive (Gamma0 N) →+ A) :=
  degeneracyTransfer₀Aux N q A
    (bezoutConjugator N q (Int.gcdA (q : ℤ) (N : ℤ)) (-Int.gcdB (q : ℤ) (N : ℤ))
      (bezout_of_prime_not_dvd N q hq hqN))
    (bezoutConjugator_heckeUpper_dvd N q _ _ _)

theorem degeneracyTransfer₀_apply (N q : ℕ) [NeZero q] (A : Type*) [AddCommGroup A]
    (hq : q.Prime) (hqN : ¬ q ∣ N) (φ : Additive (Gamma0 (N * q)) →+ A) :
    degeneracyTransfer₀ N q A hq hqN φ
      = degeneracyTransfer₀Aux N q A
          (bezoutConjugator N q (Int.gcdA (q : ℤ) (N : ℤ)) (-Int.gcdB (q : ℤ) (N : ℤ))
            (bezout_of_prime_not_dvd N q hq hqN))
          (bezoutConjugator_heckeUpper_dvd N q _ _ _) φ := rfl

theorem degeneracyTransfer₁_pullback_iota0 (N q : ℕ) [NeZero q] (A : Type*)
    [AddCommGroup A] (φ : Additive (Gamma0 N) →+ A) :
    degeneracyTransfer₁ N q A (pullbackHom (Ihara.ι₀ N q) φ)
      = heckeOperatorHom N q A φ := by
  show (coresHom (heckeUpper N q))
        ((pullbackHom ((iotaUpperEquiv N q).symm.toMonoidHom))
          ((pullbackHom (Ihara.ι₀ N q)) φ))
      = (coresHom (heckeUpper N q)) ((pullbackHom (heckeConj N q)) φ)
  congr 1
  refine AddMonoidHom.ext fun x => ?_
  have h1 : iotaUpperHom N q ((iotaUpperEquiv N q).symm (Additive.toMul x))
      = Additive.toMul x := (iotaUpperEquiv N q).apply_symm_apply (Additive.toMul x)
  have hpt : Ihara.ι₀ N q ((iotaUpperEquiv N q).symm (Additive.toMul x))
      = heckeConj N q (Additive.toMul x) := by
    rw [← heckeConj_iotaUpperHom N q ((iotaUpperEquiv N q).symm (Additive.toMul x)), h1]
  show φ (Additive.ofMul (Ihara.ι₀ N q
      ((iotaUpperEquiv N q).symm.toMonoidHom (Additive.toMul x))))
      = φ (Additive.ofMul (heckeConj N q (Additive.toMul x)))
  rw [MulEquiv.coe_toMonoidHom, hpt]

theorem degeneracyTransfer₀Aux_pullback_iota1 (N q : ℕ) [NeZero q] (A : Type*)
    [AddCommGroup A] (u : Gamma0 N)
    (hu : ∀ γ : Gamma0 (N * q),
      (q : ℤ) ∣ ((u * Ihara.ι₀ N q γ * u⁻¹ : Gamma0 N) : SL(2, ℤ)) 0 1)
    (φ : Additive (Gamma0 N) →+ A) :
    degeneracyTransfer₀Aux N q A u hu (pullbackHom (Ihara.ι₁ N q) φ)
      = heckeOperatorHom N q A φ := by
  have hwash : pullbackHom ((MulAut.conj u).toMonoidHom) φ = φ := by
    refine AddMonoidHom.ext fun x => ?_
    show φ (Additive.ofMul (u * Additive.toMul x * u⁻¹)) = φ x
    rw [show Additive.ofMul (u * Additive.toMul x * u⁻¹)
        = Additive.ofMul (u : Gamma0 N) + Additive.ofMul (Additive.toMul x)
          + Additive.ofMul ((u : Gamma0 N))⁻¹ from rfl]
    rw [map_add, map_add, ofMul_inv, map_neg]
    show φ (Additive.ofMul (u : Gamma0 N)) + φ x + -φ (Additive.ofMul (u : Gamma0 N)) = φ x
    abel
  have key : (pullbackHom (alConjHom N q u hu)) ((pullbackHom (Ihara.ι₁ N q)) φ)
      = (pullbackHom (Ihara.ι₀ N q)) (pullbackHom ((MulAut.conj u).toMonoidHom) φ) := by
    refine AddMonoidHom.ext fun x => ?_
    show φ (Additive.ofMul (Ihara.ι₁ N q (alConjHom N q u hu (Additive.toMul x))))
        = φ (Additive.ofMul ((MulAut.conj u) (Ihara.ι₀ N q (Additive.toMul x))))
    rw [iota1_alConjHom]
    rfl
  show degeneracyTransfer₁ N q A ((pullbackHom (alConjHom N q u hu))
      ((pullbackHom (Ihara.ι₁ N q)) φ)) = heckeOperatorHom N q A φ
  rw [key, hwash]
  exact degeneracyTransfer₁_pullback_iota0 N q A φ

def alConjSqMat (N q : ℕ) (a b : ℤ) : Matrix (Fin 2) (Fin 2) ℤ :=
  !![(q : ℤ) * a ^ 2 + (N : ℤ) * b, b * (a + 1);
     (N : ℤ) * (q : ℤ) * (a + 1), (N : ℤ) * b + (q : ℤ)]

theorem alConjSqMat_det (N q : ℕ) (a b : ℤ) (hab : (q : ℤ) * a - (N : ℤ) * b = 1) :
    Matrix.det (alConjSqMat N q a b) = 1 := by
  rw [alConjSqMat, Matrix.det_fin_two_of]
  linear_combination ((q : ℤ) * a - (N : ℤ) * b + 1) * hab

def alConjSqElt (N q : ℕ) (a b : ℤ) (hab : (q : ℤ) * a - (N : ℤ) * b = 1) :
    Gamma0 (N * q) :=
  ⟨⟨alConjSqMat N q a b, alConjSqMat_det N q a b hab⟩, by
    refine Gamma0_mem.mpr ?_
    show ((alConjSqMat N q a b 1 0 : ℤ) : ZMod (N * q)) = 0
    show (((N : ℤ) * (q : ℤ) * (a + 1) : ℤ) : ZMod (N * q)) = 0
    have hNq : ((N : ZMod (N * q)) * (q : ZMod (N * q))) = 0 := by
      rw [← Nat.cast_mul]
      exact ZMod.natCast_self _
    push_cast
    rw [hNq, zero_mul]⟩

theorem coe_alConjHom_bezout (N q : ℕ) [NeZero q] (a b : ℤ)
    (hab : (q : ℤ) * a - (N : ℤ) * b = 1) (δ : Gamma0 (N * q)) (c₀ : ℤ)
    (hc₀ : (((δ : SL(2, ℤ)) : Matrix (Fin 2) (Fin 2) ℤ)) 1 0 = (q : ℤ) * c₀) :
    (((alConjHom N q (bezoutConjugator N q a b hab)
        (bezoutConjugator_heckeUpper_dvd N q a b hab) δ :
        Gamma0 (N * q)) : SL(2, ℤ)) : Matrix (Fin 2) (Fin 2) ℤ)
      = !![(q : ℤ) * a * (((δ : SL(2, ℤ)) : Matrix (Fin 2) (Fin 2) ℤ)) 0 0
            + b * ((q : ℤ) * c₀) - (N : ℤ) * ((q : ℤ) * a * (((δ : SL(2, ℤ)) :
              Matrix (Fin 2) (Fin 2) ℤ)) 0 1 + b * (((δ : SL(2, ℤ)) :
              Matrix (Fin 2) (Fin 2) ℤ)) 1 1),
          -(a * b * (((δ : SL(2, ℤ)) : Matrix (Fin 2) (Fin 2) ℤ)) 0 0) - b ^ 2 * c₀
            + (q : ℤ) * a ^ 2 * (((δ : SL(2, ℤ)) : Matrix (Fin 2) (Fin 2) ℤ)) 0 1
            + a * b * (((δ : SL(2, ℤ)) : Matrix (Fin 2) (Fin 2) ℤ)) 1 1;
          ((N : ℤ) * (((δ : SL(2, ℤ)) : Matrix (Fin 2) (Fin 2) ℤ)) 0 0 + (q : ℤ) * c₀
            - (N : ℤ) ^ 2 * (((δ : SL(2, ℤ)) : Matrix (Fin 2) (Fin 2) ℤ)) 0 1
            - (N : ℤ) * (((δ : SL(2, ℤ)) : Matrix (Fin 2) (Fin 2) ℤ)) 1 1) * (q : ℤ),
          -((N : ℤ) * b * (((δ : SL(2, ℤ)) : Matrix (Fin 2) (Fin 2) ℤ)) 0 0)
            - b * ((q : ℤ) * c₀)
            + (N : ℤ) * (q : ℤ) * a * (((δ : SL(2, ℤ)) : Matrix (Fin 2) (Fin 2) ℤ)) 0 1
            + (q : ℤ) * a * (((δ : SL(2, ℤ)) : Matrix (Fin 2) (Fin 2) ℤ)) 1 1] := by
  have hqZ : ((q : ℕ) : ℤ) ≠ 0 := Int.natCast_ne_zero.mpr (NeZero.ne q)
  set dM := (((δ : SL(2, ℤ)) : Matrix (Fin 2) (Fin 2) ℤ)) with hdM
  have hsymm : (((alConjHom N q (bezoutConjugator N q a b hab)
      (bezoutConjugator_heckeUpper_dvd N q a b hab) δ :
      Gamma0 (N * q)) : SL(2, ℤ)) : Matrix (Fin 2) (Fin 2) ℤ)
      = !![(((conjUpperHom N q (bezoutConjugator N q a b hab)
              (bezoutConjugator_heckeUpper_dvd N q a b hab) δ :
              Gamma0 N) : SL(2, ℤ)) : Matrix (Fin 2) (Fin 2) ℤ) 0 0,
            (((conjUpperHom N q (bezoutConjugator N q a b hab)
              (bezoutConjugator_heckeUpper_dvd N q a b hab) δ :
              Gamma0 N) : SL(2, ℤ)) : Matrix (Fin 2) (Fin 2) ℤ) 0 1 / (q : ℤ);
            (((conjUpperHom N q (bezoutConjugator N q a b hab)
              (bezoutConjugator_heckeUpper_dvd N q a b hab) δ :
              Gamma0 N) : SL(2, ℤ)) : Matrix (Fin 2) (Fin 2) ℤ) 1 0 * (q : ℤ),
            (((conjUpperHom N q (bezoutConjugator N q a b hab)
              (bezoutConjugator_heckeUpper_dvd N q a b hab) δ :
              Gamma0 N) : SL(2, ℤ)) : Matrix (Fin 2) (Fin 2) ℤ) 1 1] :=
    coe_iotaUpperEquiv_symm N q _
  rw [hsymm]
  have hcu : (((conjUpperHom N q (bezoutConjugator N q a b hab)
      (bezoutConjugator_heckeUpper_dvd N q a b hab) δ :
      Gamma0 N) : SL(2, ℤ)) : Matrix (Fin 2) (Fin 2) ℤ)
      = (!![(q : ℤ) * a, b; (N : ℤ), 1] : Matrix (Fin 2) (Fin 2) ℤ) * dM
        * (!![1, -b; -(N : ℤ), (q : ℤ) * a] : Matrix (Fin 2) (Fin 2) ℤ) := by
    show ((((bezoutConjugator N q a b hab : Gamma0 N) * Ihara.ι₀ N q δ *
        (bezoutConjugator N q a b hab)⁻¹ : Gamma0 N) : SL(2, ℤ)) :
          Matrix (Fin 2) (Fin 2) ℤ) = _
    have h1 : ((((bezoutConjugator N q a b hab : Gamma0 N) * Ihara.ι₀ N q δ *
        (bezoutConjugator N q a b hab)⁻¹ : Gamma0 N) : SL(2, ℤ)) :
          Matrix (Fin 2) (Fin 2) ℤ)
        = (((bezoutConjugator N q a b hab : Gamma0 N) : SL(2, ℤ)) :
            Matrix (Fin 2) (Fin 2) ℤ)
          * dM * ((((bezoutConjugator N q a b hab : Gamma0 N) : SL(2, ℤ))⁻¹ : SL(2, ℤ)) :
            Matrix (Fin 2) (Fin 2) ℤ) := rfl
    rw [h1, Matrix.SpecialLinearGroup.SL2_inv_expl]
    rfl
  have hexp : ((!![(q : ℤ) * a, b; (N : ℤ), 1] : Matrix (Fin 2) (Fin 2) ℤ) * dM
      * (!![1, -b; -(N : ℤ), (q : ℤ) * a] : Matrix (Fin 2) (Fin 2) ℤ)) 0 1
      = (q : ℤ) * (-(a * b * dM 0 0) - b ^ 2 * c₀ + (q : ℤ) * a ^ 2 * dM 0 1
          + a * b * dM 1 1) := by
    simp [Matrix.mul_apply, Fin.sum_univ_two, Matrix.vecMul, Matrix.vecHead, Matrix.vecTail]
    rw [hc₀]
    ring
  rw [hcu]
  ext i j
  fin_cases i <;> fin_cases j
  · simp [Matrix.mul_apply, Fin.sum_univ_two, Matrix.vecMul, Matrix.vecHead, Matrix.vecTail,
      hc₀]
    ring
  · show ((!![(q : ℤ) * a, b; (N : ℤ), 1] : Matrix (Fin 2) (Fin 2) ℤ) * dM
        * (!![1, -b; -(N : ℤ), (q : ℤ) * a] : Matrix (Fin 2) (Fin 2) ℤ)) 0 1 / (q : ℤ) = _
    rw [hexp, Int.mul_ediv_cancel_left _ hqZ]
    simp
  · simp [Matrix.mul_apply, Fin.sum_univ_two, Matrix.vecMul, Matrix.vecHead, Matrix.vecTail,
      hc₀]
    left
    ring
  · simp [Matrix.mul_apply, Fin.sum_univ_two, Matrix.vecMul, Matrix.vecHead, Matrix.vecTail,
      hc₀]
    ring

theorem alConjHom_bezout_sq (N q : ℕ) [NeZero q] (a b : ℤ)
    (hab : (q : ℤ) * a - (N : ℤ) * b = 1) (δ : Gamma0 (N * q)) :
    alConjHom N q (bezoutConjugator N q a b hab)
      (bezoutConjugator_heckeUpper_dvd N q a b hab)
      (alConjHom N q (bezoutConjugator N q a b hab)
        (bezoutConjugator_heckeUpper_dvd N q a b hab) δ)
      = alConjSqElt N q a b hab * δ * (alConjSqElt N q a b hab)⁻¹ := by
  have hqZ : ((q : ℕ) : ℤ) ≠ 0 := Int.natCast_ne_zero.mpr (NeZero.ne q)
  obtain ⟨c₀, hc₀⟩ := Ihara.q_dvd_entry N q δ
  set dM := (((δ : SL(2, ℤ)) : Matrix (Fin 2) (Fin 2) ℤ)) with hdM
  refine Ihara.iota1_injective N (NeZero.ne q) ?_
  rw [iota1_alConjHom, map_mul, map_mul, map_inv]
  refine Subtype.ext (Subtype.ext ?_)
  show ((((bezoutConjugator N q a b hab : Gamma0 N) : SL(2, ℤ)) :
      Matrix (Fin 2) (Fin 2) ℤ) *
      (((Ihara.ι₀ N q (alConjHom N q (bezoutConjugator N q a b hab)
          (bezoutConjugator_heckeUpper_dvd N q a b hab) δ) : Gamma0 N) : SL(2, ℤ)) :
        Matrix (Fin 2) (Fin 2) ℤ) *
      ((((bezoutConjugator N q a b hab : Gamma0 N) : SL(2, ℤ))⁻¹ : SL(2, ℤ)) :
        Matrix (Fin 2) (Fin 2) ℤ))
    = ((((Ihara.ι₁ N q (alConjSqElt N q a b hab) : Gamma0 N) : SL(2, ℤ)) :
        Matrix (Fin 2) (Fin 2) ℤ) *
      (((Ihara.ι₁ N q δ : Gamma0 N) : SL(2, ℤ)) : Matrix (Fin 2) (Fin 2) ℤ) *
      ((((Ihara.ι₁ N q (alConjSqElt N q a b hab) : Gamma0 N) : SL(2, ℤ))⁻¹ : SL(2, ℤ)) :
        Matrix (Fin 2) (Fin 2) ℤ))
  have hι₀ : (((Ihara.ι₀ N q (alConjHom N q (bezoutConjugator N q a b hab)
      (bezoutConjugator_heckeUpper_dvd N q a b hab) δ) : Gamma0 N) : SL(2, ℤ)) :
        Matrix (Fin 2) (Fin 2) ℤ)
      = (((alConjHom N q (bezoutConjugator N q a b hab)
          (bezoutConjugator_heckeUpper_dvd N q a b hab) δ : Gamma0 (N * q)) : SL(2, ℤ)) :
        Matrix (Fin 2) (Fin 2) ℤ) := rfl
  rw [hι₀, coe_alConjHom_bezout N q a b hab δ c₀ hc₀]
  have hι₁δ : (((Ihara.ι₁ N q δ : Gamma0 N) : SL(2, ℤ)) : Matrix (Fin 2) (Fin 2) ℤ)
      = !![dM 0 0, dM 0 1 * (q : ℤ); c₀, dM 1 1] := by
    rw [Ihara.coe_coe_iota1]
    ext i j
    fin_cases i <;> fin_cases j
    · rfl
    · rfl
    · show dM 1 0 / (q : ℤ) = c₀
      rw [hc₀, Int.mul_ediv_cancel_left _ hqZ]
    · rfl
  have hι₁c : (((Ihara.ι₁ N q (alConjSqElt N q a b hab) : Gamma0 N) : SL(2, ℤ)) :
      Matrix (Fin 2) (Fin 2) ℤ)
      = !![(q : ℤ) * a ^ 2 + (N : ℤ) * b, b * (a + 1) * (q : ℤ);
            (N : ℤ) * (a + 1), (N : ℤ) * b + (q : ℤ)] := by
    rw [Ihara.coe_coe_iota1]
    ext i j
    fin_cases i <;> fin_cases j
    · rfl
    · rfl
    · show (N : ℤ) * (q : ℤ) * (a + 1) / (q : ℤ) = (N : ℤ) * (a + 1)
      rw [show (N : ℤ) * (q : ℤ) * (a + 1) = (q : ℤ) * ((N : ℤ) * (a + 1)) by ring,
        Int.mul_ediv_cancel_left _ hqZ]
    · rfl
  have hinvu : ((((bezoutConjugator N q a b hab : Gamma0 N) : SL(2, ℤ))⁻¹ : SL(2, ℤ)) :
      Matrix (Fin 2) (Fin 2) ℤ) = !![1, -b; -(N : ℤ), (q : ℤ) * a] := by
    rw [Matrix.SpecialLinearGroup.SL2_inv_expl]
    rfl
  have hinvc : ((((Ihara.ι₁ N q (alConjSqElt N q a b hab) : Gamma0 N) : SL(2, ℤ))⁻¹ :
      SL(2, ℤ)) : Matrix (Fin 2) (Fin 2) ℤ)
      = !![(N : ℤ) * b + (q : ℤ), -(b * (a + 1) * (q : ℤ));
            -((N : ℤ) * (a + 1)), (q : ℤ) * a ^ 2 + (N : ℤ) * b] := by
    rw [Matrix.SpecialLinearGroup.SL2_inv_expl]
    show !![(((Ihara.ι₁ N q (alConjSqElt N q a b hab) : Gamma0 N) : SL(2, ℤ)) :
          Matrix (Fin 2) (Fin 2) ℤ) 1 1,
        -((((Ihara.ι₁ N q (alConjSqElt N q a b hab) : Gamma0 N) : SL(2, ℤ)) :
          Matrix (Fin 2) (Fin 2) ℤ) 0 1);
        -((((Ihara.ι₁ N q (alConjSqElt N q a b hab) : Gamma0 N) : SL(2, ℤ)) :
          Matrix (Fin 2) (Fin 2) ℤ) 1 0),
        (((Ihara.ι₁ N q (alConjSqElt N q a b hab) : Gamma0 N) : SL(2, ℤ)) :
          Matrix (Fin 2) (Fin 2) ℤ) 0 0] = _
    rw [hι₁c]
    ext i j
    fin_cases i <;> fin_cases j <;> rfl
  have hucoe : (((bezoutConjugator N q a b hab : Gamma0 N) : SL(2, ℤ)) :
      Matrix (Fin 2) (Fin 2) ℤ) = !![(q : ℤ) * a, b; (N : ℤ), 1] := rfl
  rw [hι₁δ, hι₁c, hinvu, hinvc, hucoe]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Matrix.mul_apply, Fin.sum_univ_two, Matrix.vecHead, Matrix.vecTail]
  · linear_combination (0 : ℤ) * hab
  · linear_combination (0 : ℤ) * hab
  · linear_combination (0 : ℤ) * hab
  · linear_combination (0 : ℤ) * hab

end HeckeEis



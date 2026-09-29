-- Prove2me | Definitions.Def_IharaAmalgamMap
-- name    : IharaAmalgamMap
-- status  : Definition
-- author  : @Claude
-- created : 2026-09-05T04:28:27.528425+00:00
-- url     : https://prove2.me/theorems/0f91d490-8480-5f44-83c3-ca25178660dc
-- title:
--   Amalgam of two Γ0​(N)'s mapped into SL2​(Z[1/q])
-- statement:
--   Fix natural numbers $N$ and $q$ and write $\mathbb{Z}[1/q]$ for `ZAway q`, the localisation of $\mathbb{Z}$ away from $q$. The module constructs the comparison homomorphism from the amalgam `iharaAmalgam N q` — the pushout of the two maps $\iota_0,\iota_1 : \Gamma_0(Nq) \to \Gamma_0(N)$, where $\iota_0$ is the inclusion and $\iota_1$ sends $\begin{pmatrix}a&b\\c&d\end{pmatrix}$ to $\begin{pmatrix}a&bq\\c/q&d\end{pmatrix}$ — into $\mathrm{SL}_2(\mathbb{Z}[1/q])$. The ingredients are: `slToAway q`, base change of matrices along $\mathbb{Z} \to \mathbb{Z}[1/q]$, injective when $q \neq 0$ because the localisation map is; `vertexZero N q`, the restriction of `slToAway q` to $\Gamma_0(N)$; and `vertexOne N q`, that map followed by conjugation $\delta \mapsto w\delta w^{-1}$ by $w = \mathrm{diag}(1,q)$, with the entrywise description $\begin{pmatrix}a&b\\c&d\end{pmatrix} \mapsto \begin{pmatrix}a&b/q\\qc&d\end{pmatrix}$ over $\mathbb{Z}[1/q]$. The identity `vertex_compat` records that `vertexZero` composed with $\iota_0$ equals `vertexOne` composed with $\iota_1$, coming from the integral relation $w\,\iota_1(\gamma) = \gamma\, w$; the universal property of the pushout then yields `amalgamToAway N q`, whose values on the two vertex copies and on the edge group are as prescribed.
--
--   Since the lower-left entry of $\gamma \in \Gamma_0(N)$ is divisible by $N$, and that of $w\gamma w^{-1}$ is $q$ times it, both vertex images lie in `Gamma0Away N q`, the subgroup of $\mathrm{SL}_2(\mathbb{Z}[1/q])$ cut out by $N \mid g_{10}$; as the vertex images generate the amalgam, the range of `amalgamToAway N q` lies in `Gamma0Away N q`, and `amalgamToGamma0Away N q` is the resulting corestricted homomorphism. Its injectivity is equivalent to that of `amalgamToAway N q`.
--
--   **Relation to Mathlib.** Mathlib supplies the amalgamated product as `Monoid.PushoutI`, base change of special linear groups as `Matrix.SpecialLinearGroup.map`, and localisation away from an element; the congruence subgroups $\Gamma_0$ over $\mathbb{Z}$ are Mathlib's `CongruenceSubgroup.Gamma0`. The amalgam `iharaAmalgam`, its vertex and edge maps, the group `Gamma0Away` over $\mathbb{Z}[1/q]$ and the comparison homomorphism are the project's own.
--
--   **Where it is used.** The homomorphism constructed here is one half of the identification of $\mathrm{SL}_2(\mathbb{Z}[1/q])$-level structures as an amalgam of two copies of $\Gamma_0(N)$ along $\Gamma_0(Nq)$, the group-theoretic input (via the action on the tree of $\mathrm{SL}_2(\mathbb{Q}_q)$) to Ihara's lemma. Ihara's lemma in turn supports the level-raising and congruence arguments used in the modularity side of the proof.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Definitions/Def_IharaAmalgamMap.lean

import Definitions.Def_IharaAmalgam
import Definitions.Def_Gamma0Away

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace Ihara

open Matrix CongruenceSubgroup

open scoped MatrixGroups

variable (N q : ℕ)

def slToAway : SL(2, ℤ) →* SL(2, ZAway q) :=
  Matrix.SpecialLinearGroup.map (algebraMap ℤ (ZAway q))

@[simp]
theorem coe_slToAway (g : SL(2, ℤ)) :
    ((slToAway q g : SL(2, ZAway q)) : Matrix (Fin 2) (Fin 2) (ZAway q)) =
      ((g : Matrix (Fin 2) (Fin 2) ℤ)).map (algebraMap ℤ (ZAway q)) :=
  rfl

theorem algebraMap_ZAway_injective {q : ℕ} (hq : q ≠ 0) :
    Function.Injective (algebraMap ℤ (ZAway q)) :=
  IsLocalization.injective (M := Submonoid.powers (q : ℤ)) (ZAway q)
    (powers_le_nonZeroDivisors_of_noZeroDivisors (Int.natCast_ne_zero.mpr hq))

theorem slToAway_injective {q : ℕ} (hq : q ≠ 0) : Function.Injective (slToAway q) := by
  intro g h hgh
  have hmat := congrArg (fun x : SL(2, ZAway q) => (x : Matrix (Fin 2) (Fin 2) (ZAway q))) hgh
  refine Subtype.ext (Matrix.ext fun i j => ?_)
  have hij := congrFun (congrFun hmat i) j
  simp only [coe_slToAway, map_apply] at hij
  exact algebraMap_ZAway_injective hq hij

def vertexZero : Gamma0 N →* SL(2, ZAway q) :=
  (slToAway q).comp (Gamma0 N).subtype

@[simp]
theorem coe_vertexZero (g : Gamma0 N) :
    ((vertexZero N q g : SL(2, ZAway q)) : Matrix (Fin 2) (Fin 2) (ZAway q)) =
      (((g : SL(2, ℤ)) : Matrix (Fin 2) (Fin 2) ℤ)).map (algebraMap ℤ (ZAway q)) :=
  rfl

noncomputable def vertexOne : Gamma0 N →* SL(2, ZAway q) :=
  (wConj q).symm.toMonoidHom.comp (vertexZero N q)

theorem coe_vertexOne (g : Gamma0 N) :
    ((vertexOne N q g : SL(2, ZAway q)) : Matrix (Fin 2) (Fin 2) (ZAway q)) =
      wMat q * (((g : SL(2, ℤ)) : Matrix (Fin 2) (Fin 2) ℤ)).map (algebraMap ℤ (ZAway q)) *
        wMatInv q :=
  rfl

theorem wMat_mul_mul_wMatInv (M : Matrix (Fin 2) (Fin 2) (ZAway q)) :
    wMat q * M * wMatInv q =
      !![M 0 0, M 0 1 * IsLocalization.Away.invSelf (S := ZAway q) (q : ℤ);
         (q : ZAway q) * M 1 0, M 1 1] := by
  conv_lhs => rw [Matrix.eta_fin_two M]
  rw [wMat, wMatInv, Matrix.mul_fin_two, Matrix.mul_fin_two]
  simp only [one_mul, zero_mul, mul_zero, add_zero, zero_add, mul_one]
  rw [mul_right_comm (q : ZAway q) (M 1 1), q_mul_invSelf, one_mul]

theorem coe_vertexOne_eq (g : Gamma0 N) :
    ((vertexOne N q g : SL(2, ZAway q)) : Matrix (Fin 2) (Fin 2) (ZAway q)) =
      !![algebraMap ℤ (ZAway q) ((g : SL(2, ℤ)) 0 0),
         algebraMap ℤ (ZAway q) ((g : SL(2, ℤ)) 0 1) *
           IsLocalization.Away.invSelf (S := ZAway q) (q : ℤ);
         (q : ZAway q) * algebraMap ℤ (ZAway q) ((g : SL(2, ℤ)) 1 0),
         algebraMap ℤ (ZAway q) ((g : SL(2, ℤ)) 1 1)] := by
  rw [coe_vertexOne, wMat_mul_mul_wMatInv]
  rfl

theorem map_wInt_eq_wMat :
    (!![(1 : ℤ), 0; 0, (q : ℤ)]).map (algebraMap ℤ (ZAway q)) = wMat q := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [wMat]

theorem vertex_compat : (vertexZero N q).comp (ι₀ N q) = (vertexOne N q).comp (ι₁ N q) := by
  ext γ : 1
  apply Subtype.ext
  show (((γ : SL(2, ℤ)) : Matrix (Fin 2) (Fin 2) ℤ)).map (algebraMap ℤ (ZAway q)) =
    wMat q * ((((ι₁ N q γ : Gamma0 N) : SL(2, ℤ)) : Matrix (Fin 2) (Fin 2) ℤ)).map
      (algebraMap ℤ (ZAway q)) * wMatInv q
  have h := congrArg (fun M : Matrix (Fin 2) (Fin 2) ℤ => M.map (algebraMap ℤ (ZAway q)))
    (w_mul_iota1 N q γ)
  simp only [Matrix.map_mul, map_wInt_eq_wMat] at h
  rw [h, mul_assoc, wMat_mul_wMatInv, mul_one]

noncomputable def amalgamToAway : iharaAmalgam N q →* SL(2, ZAway q) :=
  iharaLift (vertexZero N q) (vertexOne N q) (vertex_compat N q)

theorem amalgamToAway_vertex_zero (g : Gamma0 N) :
    amalgamToAway N q (iharaVertex N q 0 g) = vertexZero N q g :=
  iharaLift_vertex_zero _ _ _ g

theorem amalgamToAway_vertex_one (g : Gamma0 N) :
    amalgamToAway N q (iharaVertex N q 1 g) = vertexOne N q g :=
  iharaLift_vertex_one _ _ _ g

theorem amalgamToAway_base (γ : Gamma0 (N * q)) :
    amalgamToAway N q (iharaBase N q γ) = slToAway q γ :=
  iharaLift_base _ _ _ γ

theorem N_dvd_entry (g : Gamma0 N) : (N : ℤ) ∣ (g : SL(2, ℤ)) 1 0 := by
  have h := g.2
  rw [Gamma0_mem, CharP.intCast_eq_zero_iff (ZMod N) N] at h
  exact h

theorem vertexZero_mem (g : Gamma0 N) : vertexZero N q g ∈ Gamma0Away N q := by
  obtain ⟨k, hk⟩ := N_dvd_entry N g
  refine ⟨algebraMap ℤ (ZAway q) k, ?_⟩
  show algebraMap ℤ (ZAway q) ((g : SL(2, ℤ)) 1 0) = _
  rw [hk, map_mul]
  simp

theorem vertexOne_apply_one_zero (g : Gamma0 N) :
    (vertexOne N q g : SL(2, ZAway q)) 1 0 =
      (q : ZAway q) * algebraMap ℤ (ZAway q) ((g : SL(2, ℤ)) 1 0) := by
  rw [coe_vertexOne_eq]
  rfl

theorem vertexOne_mem (g : Gamma0 N) : vertexOne N q g ∈ Gamma0Away N q := by
  rw [mem_Gamma0Away, vertexOne_apply_one_zero]
  obtain ⟨k, hk⟩ := N_dvd_entry N g
  refine ⟨(q : ZAway q) * algebraMap ℤ (ZAway q) k, ?_⟩
  rw [hk, map_mul, eq_intCast, Int.cast_natCast]
  ring

theorem range_amalgamToAway_le : (amalgamToAway N q).range ≤ Gamma0Away N q := by
  rw [MonoidHom.range_eq_map, ← iharaVertex_range_sup, Subgroup.map_sup, sup_le_iff,
    MonoidHom.map_range, MonoidHom.map_range]
  constructor
  · rintro _ ⟨g, rfl⟩
    rw [MonoidHom.comp_apply, amalgamToAway_vertex_zero]
    exact vertexZero_mem N q g
  · rintro _ ⟨g, rfl⟩
    rw [MonoidHom.comp_apply, amalgamToAway_vertex_one]
    exact vertexOne_mem N q g

theorem amalgamToAway_mem (x : iharaAmalgam N q) : amalgamToAway N q x ∈ Gamma0Away N q :=
  range_amalgamToAway_le N q ⟨x, rfl⟩

noncomputable def amalgamToGamma0Away : iharaAmalgam N q →* Gamma0Away N q :=
  (amalgamToAway N q).codRestrict (Gamma0Away N q) (amalgamToAway_mem N q)

@[simp]
theorem coe_amalgamToGamma0Away (x : iharaAmalgam N q) :
    ((amalgamToGamma0Away N q x : Gamma0Away N q) : SL(2, ZAway q)) = amalgamToAway N q x :=
  rfl

theorem amalgamToGamma0Away_injective_iff :
    Function.Injective (amalgamToGamma0Away N q) ↔ Function.Injective (amalgamToAway N q) :=
  MonoidHom.injective_codRestrict _ _ _

end Ihara



-- Prove2me | Definitions.Def_DetANN_Thm11_RawAssemblyTables
-- name    : DetANN_Thm11_RawAssemblyTables
-- status  : Definition
-- author  : @Mr Robbins
-- created : 2026-11-23T05:42:29.876682+00:00
-- url     : https://prove2.me/theorems/20ad582a-1da8-4a0f-a050-c69a873b190f
-- title:
--   Raw outer-assembly bounds, even MGG walk tables, and linear even padding
-- statement:
--   This module fixes implementation data for the raw machine assembly used in §§7.1–7.4. `RawLocalAnswer C₀ k P ε q a` says that, for every tuple $v\in[2^k]$, a local representative $r_v$ is $(1+\varepsilon/100)$-nearest in the projected list and that the original-space candidate $P_a$ is no farther from $q$ than any of these representatives. `rawPreCost` and `rawQueryCost` are explicit, deliberately unoptimised resource envelopes for the preprocessing and query glue and for the calls to the supplied low-dimensional structure.
--
--   The padding is uniform and even: if `r = evenPadRadius d` is the least natural number with $d\le4^r$, then `evenPadExp d = 2r`. Proved structural lemmas give $d\le2^k$ for $k=2r$, $2^k<4d$ when $d>1$, and $2^k=1$ at $d=1$. The minimizer keeps these inequalities at their exact integer boundary with no rounding.
--
--   For the expander tables, `mggNbrN` is a wholly arithmetic implementation of the eight Margulis–Gabber–Galil neighbours on $\mathbb Z_m^2$, and `nbrN r` is the neighbour map on $[2^{2r}]$ under $v=x2^r+y$. In even dimension the two copies of the eight MGG edges coincide, so an edge choice $o<16$ depends only on $o\bmod8$; `nbrN_spec` proves exact agreement with the published `lemma71Nbr (2*r)`. A walk code uses little-endian base 16, with the first edge equal to `code % 16` and the remaining code equal to `code / 16`. `walkEndCode` follows these choices, and `walkEndCode_spec` proves that its endpoint equals the abstract `walkEnd` on `walkWord`. `walkTable r ℓ` lists these endpoints with tuple major and walk code minor, and its lookup spec identifies every entry with the corresponding walk endpoint. These are finite tables that preprocessing can materialize directly in integer memory.
-- source:
--   Y. Feng, P. Indyk, STOC 2027 submission #1254: §7.1 (p.16) for the tuple family and walk occurrences; §7.4 (p.18) for local solutions and taking the closest returned original-space representative; Lemma 7.1 and Appendix B (pp.17,20) for the explicit 16-regular Margulis–Gabber–Galil graph. The even padding and machine-oriented natural-number encodings are implementation refinements: the published graph at even dimension is exactly the two-copy 16-regular multigraph on $2^{2r}$ vertices. Resource expressions follow Lemma 3.3 (p.7) and the composition in §7.4.

import Mathlib
import Definitions.Def_PNormReg_Machine
import Definitions.Def_DetANN_DataStructure
import Definitions.Def_DetANN_Construction
import Definitions.Def_DetANN_TupleFamily
import Definitions.Def_DetANN_Thm11_Split
import Definitions.Def_DetANN_Thm11_LocalProjection

namespace DetANN.Thm11

/-- The answer produced by the raw outer assembly: all local answers and an original-space
candidate no farther than any of their representatives. -/
noncomputable def RawLocalAnswer {d n : ℕ} (C₀ : ℝ) (k : ℕ)
    (P : Fin n → EuclideanSpace ℝ (Fin d)) (ε : ℝ)
    (q : EuclideanSpace ℝ (Fin d)) (a : Fin n) : Prop :=
  ∃ r : ∀ v : Fin (2 ^ k), Fin (projectedSet C₀ k P ε v).card,
    (∀ (v : Fin (2 ^ k)) (j : Fin (projectedSet C₀ k P ε v).card),
      ‖annProject C₀ k P ε v (padVec (2 ^ k) q) - localData C₀ k P ε v (r v)‖ ≤
        (1 + ε / 100) *
          ‖annProject C₀ k P ε v (padVec (2 ^ k) q) - localData C₀ k P ε v j‖) ∧
    ∀ v, ‖q - P a‖ ≤ ‖q - P (localRepIdx C₀ k P ε v (r v))‖

/-- The common polynomial glue term in the raw preprocessing estimate. -/
noncomputable def rawGlueBase {d n : ℕ} (C₀ : ℝ) (k : ℕ)
    (P : Fin n → EuclideanSpace ℝ (Fin d)) (ε : ℝ) : ℝ :=
  ((n + 2 ^ k + annDim C₀ k P ε +
    momentOrder (diffSet k P).card (2 ^ k) + 16 ^ walkLen ε + 1 : ℕ) : ℝ)

/-- The supplied Lemma 3.3 preprocessing-time bound, evaluated at `N = n`. -/
noncomputable def rawInnerPreTime {d n : ℕ} (C : ℝ) (K C' : ℕ) (C₀ : ℝ) (k : ℕ)
    (P : Fin n → EuclideanSpace ℝ (Fin d)) (ε : ℝ) : ℝ :=
  (C' : ℝ) * ((n : ℝ) + annDim C₀ k P ε) ^ K *
    (C / (ε / 100)) ^ ((K : ℝ) * (annDim C₀ k P ε : ℝ)) *
      Real.log ((n : ℝ) / (ε / 100)) ^ K

/-- The supplied Lemma 3.3 space bound, evaluated at `N = n`. -/
noncomputable def rawInnerSpace {d n : ℕ} (C : ℝ) (K C' : ℕ) (C₀ : ℝ) (k : ℕ)
    (P : Fin n → EuclideanSpace ℝ (Fin d)) (ε : ℝ) : ℝ :=
  (C' : ℝ) * (n : ℝ) *
    (C / (ε / 100)) ^ ((K : ℝ) * (annDim C₀ k P ε : ℝ)) *
      Real.log ((n : ℝ) / (ε / 100)) ^ K

/-- Explicit unoptimised preprocessing bound for the outer construction. -/
noncomputable def rawPreCost {d n : ℕ} (C : ℝ) (K C' : ℕ) (Cw Kw : ℕ) (C₀ : ℝ) (k : ℕ)
    (P : Fin n → EuclideanSpace ℝ (Fin d)) (ε : ℝ) : ℝ :=
  (Cw : ℝ) * (rawGlueBase C₀ k P ε ^ Kw + (2 : ℝ) ^ k *
    (rawInnerPreTime C K C' C₀ k P ε + rawInnerSpace C K C' C₀ k P ε))

/-- Explicit unoptimised query bound: block evaluation, projection gathering, local queries,
and original-space comparison. -/
noncomputable def rawQueryCost {d n : ℕ} (C : ℝ) (K C' : ℕ) (Cw : ℕ) (C₀ : ℝ) (k : ℕ)
    (P : Fin n → EuclideanSpace ℝ (Fin d)) (ε : ℝ) : ℝ :=
  (Cw : ℝ) * ((2 : ℝ) ^ k *
      (((1 : ℝ) + annDim C₀ k P ε) * (1 + k) + d) +
    (2 : ℝ) ^ k * ((C' : ℝ) * (annDim C₀ k P ε : ℝ) ^ 2 *
      Real.log ((n : ℝ) / (ε / 100)) ^ 2))

end DetANN.Thm11

namespace DetANN.MGGEven

/-- The eight MGG edges in ordinary natural-number modular arithmetic. -/
def mggNbrN (m x y o : ℕ) : ℕ × ℕ :=
  match o with
  | 0 => ((x + 2*y) % m, y)
  | 1 => ((x + 2*m - 2*y) % m, y)
  | 2 => ((x + 2*y + 1) % m, y)
  | 3 => ((x + 3*m - (2*y + 1)) % m, y)
  | 4 => (x, (y + 2*x) % m)
  | 5 => (x, (y + 2*m - 2*x) % m)
  | 6 => (x, (y + 2*x + 1) % m)
  | _ => (x, (y + 3*m - (2*x + 1)) % m)

/-- In even dimension the two copies of the eight MGG edges coincide, so only `o % 8` enters. -/
def nbrN (r v o : ℕ) : ℕ :=
  let m := 2 ^ (2*r/2)
  let p := mggNbrN m (v/m) (v%m) (o%8)
  p.1*m+p.2

private lemma val_cast (m a : ℕ) : ((a : ZMod m)).val = a % m := by
  by_cases h : m = 0
  · subst m; simp
  · letI : NeZero m := ⟨h⟩
    exact ZMod.val_natCast (n := m) a

private lemma val_add_two (m x y : ℕ) :
    (((x : ZMod m) + 2 * (y : ZMod m)).val) = (x + 2*y) % m := by
  have h : ((x : ZMod m) + 2 * (y : ZMod m)) = ((x + 2*y : ℕ) : ZMod m) := by
    push_cast; rfl
  rw [h, val_cast]

private lemma val_sub_two (m x y : ℕ) (hy : y < m) :
    (((x : ZMod m) - 2 * (y : ZMod m)).val) = (x + 2*m - 2*y) % m := by
  have h : ((x : ZMod m) - 2 * (y : ZMod m)) = ((x + 2*m - 2*y : ℕ) : ZMod m) := by
    have hy2 : 2*y ≤ x + 2*m := by omega
    rw [Nat.cast_sub hy2]
    push_cast
    simp [sub_eq_add_neg]
  rw [h, val_cast]

private lemma val_add_two_one (m x y : ℕ) :
    (((x : ZMod m) + (2 * (y : ZMod m) + 1)).val) = (x + (2*y + 1)) % m := by
  have h : ((x : ZMod m) + (2 * (y : ZMod m) + 1)) = ((x + (2*y + 1) : ℕ) : ZMod m) := by
    push_cast; rfl
  rw [h, val_cast]

private lemma val_sub_two_one (m x y : ℕ) (hy : y < m) :
    (((x : ZMod m) - (2 * (y : ZMod m) + 1)).val) = (x + 3*m - (2*y + 1)) % m := by
  have h : ((x : ZMod m) - (2 * (y : ZMod m) + 1)) = ((x + 3*m - (2*y + 1) : ℕ) : ZMod m) := by
    have hy2 : 2*y+1 ≤ x + 3*m := by omega
    rw [Nat.cast_sub hy2]
    push_cast
    simp [sub_eq_add_neg]
  rw [h, val_cast]

lemma mggNbrN_spec (m x y : ℕ) (hx : x < m) (hy : y < m) (o : Fin 8) :
    (mggNbr m ((x : ℕ), (y : ℕ)) o).1.val = (mggNbrN m x y o).1 ∧
    (mggNbr m ((x : ℕ), (y : ℕ)) o).2.val = (mggNbrN m x y o).2 := by
  fin_cases o <;>
    simp [mggNbr, mggNbrN, val_add_two, val_sub_two, val_add_two_one, val_sub_two_one,
      hx, hy, Nat.add_assoc, Nat.mod_eq_of_lt]

private lemma zmod_finEquiv_apply (m : ℕ) [NeZero m] (x : Fin m) :
    (ZMod.finEquiv m) x = (x : ℕ) := by
  cases m with
  | zero => exact (Nat.not_lt_zero _ x.isLt).elim
  | succ m =>
    apply ZMod.val_injective
    change x.val = ((x.val : ℕ) : ZMod (m+1)).val
    exact (ZMod.val_cast_of_lt x.isLt).symm

private lemma zmod_finEquiv_symm_val (m : ℕ) [NeZero m] (x : ZMod m) :
    ((ZMod.finEquiv m).symm x).val = x.val := by
  cases m with
  | zero => exact (NeZero.ne 0 rfl).elim
  | succ m => rfl

private lemma equiv_even_fwd_x (r : ℕ) (v : Fin (2 ^ (2*r))) :
    (lemma71Equiv (2*r) v).1 = (v.val / 2^r : ℕ) := by
  simp [lemma71Equiv, finProdFinEquiv_symm_apply, Fin.divNat, zmod_finEquiv_apply]

private lemma equiv_even_fwd_y (r : ℕ) (v : Fin (2 ^ (2*r))) :
    (lemma71Equiv (2*r) v).2.1 = (v.val % 2^r : ℕ) := by
  simp [lemma71Equiv, finProdFinEquiv_symm_apply, Fin.modNat, Fin.divNat,
    zmod_finEquiv_apply]

private lemma equiv_even_bwd (r : ℕ) (x y : ZMod (2^(2*r/2))) :
    ((lemma71Equiv (2*r)).symm (x,y,0)).val = x.val*2^(2*r/2)+y.val := by
  have hr : 2*r/2 = r := by omega
  simp [lemma71Equiv, finProdFinEquiv_apply_val, zmod_finEquiv_symm_val, Nat.mul_comm]
  omega

/-- The natural-number edge map is exactly the published even-dimensional MGG edge map. -/
lemma nbrN_spec (r v o : ℕ) (hv : v < 2^(2*r)) (ho : o < 16) :
    (lemma71Nbr (2*r) ⟨v,hv⟩ ⟨o,ho⟩).val = nbrN r v o := by
  let m := 2^(2*r/2)
  have hr : 2*r/2 = r := by omega
  have hr0 : 2*r%2 = 0 := by omega
  have hm : 0 < m := pow_pos (by omega) _
  have hmm : m*m = 2^(2*r) := by
    dsimp [m]
    rw [hr, ← pow_add]
    congr 1
    omega
  have hx : v/m < m := (Nat.div_lt_iff_lt_mul hm).2 (hmm ▸ hv)
  have hy : v%m < m := Nat.mod_lt _ hm
  simp only [lemma71Nbr, lemma71Base]
  rw [equiv_even_fwd_x, equiv_even_fwd_y]
  have hs := mggNbrN_spec m (v/m) (v%m) hx hy ⟨o%8,Nat.mod_lt _ (by omega)⟩
  have hb := equiv_even_bwd r
    (mggNbr m ((v/m : ℕ), (v%m : ℕ)) ⟨o%8,Nat.mod_lt _ (by omega)⟩).1
    (mggNbr m ((v/m : ℕ), (v%m : ℕ)) ⟨o%8,Nat.mod_lt _ (by omega)⟩).2
  rw [hs.1, hs.2] at hb
  have hfin : (⟨o / 8 % (2*r%2+1), Nat.mod_lt _ (by omega)⟩ : Fin (2*r%2+1)) = 0 := by
    apply Fin.ext
    change o / 8 % (2*r%2+1) = 0
    rw [hr0]
    exact Nat.mod_one _
  rw [hfin]
  simpa [nbrN, m, hr] using hb

lemma nbrN_r_zero (o : ℕ) : nbrN 0 0 o = 0 := by
  have h : mggNbrN 1 0 0 (o%8) = (0,0) := by
    unfold mggNbrN
    split <;> rfl
  simp [nbrN, h]

/-- Little-endian base-16 walk codes: the first choice is `code % 16`. -/
def walkDigit (code i : ℕ) : ℕ := code / 16 ^ i % 16

def walkWord (ℓ code : ℕ) : Fin ℓ → Fin 16 := fun i =>
  ⟨walkDigit code i, Nat.mod_lt _ (by omega)⟩

/-- Follow a base-16-coded walk using a natural-number neighbor function. -/
def walkEndCode (nbr : ℕ → ℕ → ℕ) : ℕ → ℕ → ℕ → ℕ
  | 0, v, _ => v
  | ℓ + 1, v, code => walkEndCode nbr ℓ (nbr v (code % 16)) (code / 16)

lemma walkWord_zero (ℓ code : ℕ) :
    (walkWord (ℓ + 1) code 0).val = code % 16 := by
  simp [walkWord, walkDigit]

lemma walkWord_tail (ℓ code : ℕ) (i : Fin ℓ) :
    (Fin.tail (walkWord (ℓ + 1) code) i).val = (walkWord ℓ (code / 16) i).val := by
  simp [walkWord, walkDigit, Fin.tail, Nat.div_div_eq_div_mul, pow_succ, Nat.mul_comm]

lemma walkEndCode_spec {D : ℕ} (f : ℕ → ℕ → ℕ) (nbr : Fin D → Fin 16 → Fin D)
    (hf : ∀ v o (hv : v < D) (ho : o < 16), (nbr ⟨v, hv⟩ ⟨o, ho⟩).val = f v o) :
    ∀ ℓ v code (hv : v < D),
      (walkEnd nbr ℓ ⟨v, hv⟩ (walkWord ℓ code)).val = walkEndCode f ℓ v code := by
  intro ℓ
  induction ℓ with
  | zero => intro v code hv; rfl
  | succ ℓ ih =>
    intro v code hv
    rw [walkEnd, walkEndCode]
    let o : ℕ := code % 16
    have ho : o < 16 := Nat.mod_lt _ (by omega)
    have hn : (nbr ⟨v, hv⟩ ⟨o, ho⟩).val = f v o := hf v o hv ho
    let hv' : f v o < D := hn ▸ (nbr ⟨v, hv⟩ ⟨o, ho⟩).isLt
    have hw : walkWord (ℓ + 1) code 0 = ⟨o, ho⟩ := by
      apply Fin.ext
      exact walkWord_zero ℓ code
    have hstart : nbr ⟨v, hv⟩ (walkWord (ℓ + 1) code 0) = ⟨f v o, hv'⟩ := by
      rw [hw]
      apply Fin.ext
      exact hn
    have hword : Fin.tail (walkWord (ℓ + 1) code) = walkWord ℓ (code / 16) := by
      funext i
      apply Fin.ext
      exact walkWord_tail ℓ code i
    rw [hstart, hword]
    exact ih (f v o) (code / 16) hv'

/-- The endpoint table, with tuple `v` major and walk code `code` minor. -/
def walkTable (r ℓ : ℕ) : List (List ℕ) :=
  List.ofFn fun v : Fin (2 ^ (2 * r)) =>
    List.ofFn fun code : Fin (16 ^ ℓ) => walkEndCode (nbrN r) ℓ v code

lemma walkTable_length (r ℓ : ℕ) : (walkTable r ℓ).length = 2 ^ (2 * r) := by
  simp [walkTable]

lemma walkTable_row_length (r ℓ : ℕ) (v : Fin (2 ^ (2 * r))) :
    ((walkTable r ℓ).getD v []).length = 16 ^ ℓ := by
  simp [walkTable, List.getD_eq_getElem?_getD]

lemma walkTable_get (r ℓ : ℕ) (v : Fin (2 ^ (2 * r))) (code : Fin (16 ^ ℓ)) :
    ((walkTable r ℓ).getD v []).getD code 0 =
      walkEndCode (nbrN r) ℓ v code := by
  simp [walkTable, List.getD_eq_getElem?_getD]

/-- Every table entry is exactly the endpoint occurring in the paper's walk family. -/
lemma walkTable_spec (r ℓ : ℕ) (v : Fin (2 ^ (2 * r))) (code : Fin (16 ^ ℓ)) :
    ((walkTable r ℓ).getD v []).getD code 0 =
      (walkEnd (lemma71Nbr (2 * r)) ℓ v (walkWord ℓ code)).val := by
  rw [walkTable_get, walkEndCode_spec (nbrN r) (lemma71Nbr (2 * r))]
  intro u o hu ho
  exact nbrN_spec r u o hu ho

lemma evenPadExists (d : ℕ) : ∃ r : ℕ, d ≤ 4 ^ r :=
  ⟨d, (Nat.lt_pow_self (n := d) (a := 4) (by omega)).le⟩

/-- Least even exponent `k = 2r` with `d ≤ 2^k`. -/
noncomputable def evenPadRadius (d : ℕ) : ℕ := Nat.find (evenPadExists d)

noncomputable def evenPadExp (d : ℕ) : ℕ := 2 * evenPadRadius d

lemma le_four_pow_evenPadRadius (d : ℕ) : d ≤ 4 ^ evenPadRadius d :=
  Nat.find_spec (evenPadExists d)

lemma two_pow_evenPadExp (d : ℕ) : 2 ^ evenPadExp d = 4 ^ evenPadRadius d := by
  rw [evenPadExp, pow_mul]
  norm_num

lemma le_two_pow_evenPadExp (d : ℕ) : d ≤ 2 ^ evenPadExp d := by
  rw [two_pow_evenPadExp]
  exact le_four_pow_evenPadRadius d

lemma four_pow_pred_evenPadRadius_lt {d : ℕ} (hd : 1 < d) :
    4 ^ (evenPadRadius d - 1) < d := by
  have hr : evenPadRadius d ≠ 0 := by
    intro hr
    have h := le_four_pow_evenPadRadius d
    rw [hr, pow_zero] at h
    omega
  obtain ⟨s, hs⟩ := Nat.exists_eq_succ_of_ne_zero hr
  have hnot : ¬ d ≤ 4 ^ s := by
    intro h
    have hm := Nat.find_min' (evenPadExists d) h
    change evenPadRadius d ≤ s at hm
    omega
  have hlt : 4 ^ s < d := Nat.lt_of_not_ge hnot
  simpa [hs] using hlt

/-- The even padding is linear: `2^k < 4d` for `d > 1`. -/
lemma two_pow_evenPadExp_lt {d : ℕ} (hd : 1 < d) :
    2 ^ evenPadExp d < 4 * d := by
  rw [two_pow_evenPadExp]
  obtain ⟨s, hs⟩ := Nat.exists_eq_succ_of_ne_zero (by
    intro hr
    have h := le_four_pow_evenPadRadius d
    rw [hr, pow_zero] at h
    omega : evenPadRadius d ≠ 0)
  have hlt : 4 ^ s < d := by
    have h := four_pow_pred_evenPadRadius_lt hd
    simpa [hs] using h
  rw [hs, pow_succ]
  omega

lemma two_pow_evenPadExp_one : 2 ^ evenPadExp 1 = 1 := by
  have hr : evenPadRadius 1 ≤ 0 := Nat.find_min' (evenPadExists 1) (show 1 ≤ 4 ^ 0 by simp)
  have hr0 : evenPadRadius 1 = 0 := by omega
  simp [evenPadExp, hr0]

end DetANN.MGGEven



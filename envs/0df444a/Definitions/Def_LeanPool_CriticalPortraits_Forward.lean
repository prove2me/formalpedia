-- Prove2me | Definitions.Def_LeanPool_CriticalPortraits_Forward
-- name    : LeanPool_CriticalPortraits_Forward
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-21T17:25:46.571389+00:00
-- url     : https://prove2.me/theorems/a8b54b91-2e38-4416-b605-90994c20b093
-- title:
--   Forward
-- statement:
--   Definitions and structural lemmas for Forward, from Keston Aquino-Michaels; LeanPool contributors's pinned Counting critical portraits development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/CriticalPortraits/Forward.lean

module
public import Definitions.Def_LeanPool_CriticalPortraits_Core
public import Definitions.Def_LeanPool_CriticalPortraits_Portraits
public import Mathlib.Algebra.Order.Field.Basic
public import Mathlib.Data.Rat.Cast.Order
public import Mathlib.Tactic.NormNum.Abs
public import Mathlib.Tactic.NormNum.DivMod
public import Mathlib.Tactic.NormNum.OfScientific
public import Mathlib.Tactic.NormNum.Pow
public import Mathlib.Tactic.Positivity.Finset
public import Theorems.Thm_CriticalPortraits_level_injOn_fiber
public import Theorems.Thm_CriticalPortraits_linked_of_lt
public import Theorems.Thm_CriticalPortraits_mem_T
public import Theorems.Thm_CriticalPortraits_mem_eraseMin
public import Theorems.Thm_CriticalPortraits_minVal_le
public import Theorems.Thm_CriticalPortraits_sep_master
public import Theorems.Thm_CriticalPortraits_val_le_iff_level_le_of_sameFiber

set_option autoImplicit true
@[expose] public section
@[expose] public section
namespace AbstractLaminar
open Finset
variable {ι : Type*} [DecidableEq ι]
structure Family (ι : Type*) [DecidableEq ι] where
  /-- The carrier index set of the family. -/
  E : Finset ι
  /-- The low endpoint of each index. -/
  lo : ι → ℕ
  /-- The high endpoint of each index. -/
  hi : ι → ℕ
  /-- The column of each index. -/
  col : ι → ℕ
  lh : ∀ e ∈ E, lo e < hi e
  inj : ∀ e ∈ E, ∀ f ∈ E, lo e = lo f → hi e = hi f → e = f
  laminar : ∀ e ∈ E, ∀ f ∈ E, ¬ (lo e < lo f ∧ lo f < hi e ∧ hi e < hi f)
  bRight : ∀ e ∈ E, ∀ f ∈ E, hi e = hi f → lo e < lo f → col f < col e
  bLeft : ∀ e ∈ E, ∀ f ∈ E, lo e = lo f → hi f < hi e → col e < col f
  bSeam : ∀ e ∈ E, ∀ f ∈ E, hi e = lo f → col e ≤ col f
variable (fam : Family ι)
def contained (a b : ℕ) : Finset ι :=
  fam.E.filter (fun e => a ≤ fam.lo e ∧ fam.hi e ≤ b)
def N (a b : ℕ) : ℕ := (contained fam a b).card
lemma mem_contained {a b : ℕ} {e : ι} :
    e ∈ contained fam a b ↔ e ∈ fam.E ∧ a ≤ fam.lo e ∧ fam.hi e ≤ b := by
  unfold contained; rw [mem_filter]
def IsStrict (a b : ℕ) (e : ι) : Prop := fam.lo e ≠ a ∨ fam.hi e ≠ b
instance (a b : ℕ) (e : ι) : Decidable (IsStrict fam a b e) := by unfold IsStrict; infer_instance
def Sstrict (a b : ℕ) : Finset ι := (contained fam a b).filter (IsStrict fam a b)
lemma mem_Sstrict {a b : ℕ} {e : ι} :
    e ∈ Sstrict fam a b ↔ (e ∈ fam.E ∧ a ≤ fam.lo e ∧ fam.hi e ≤ b) ∧
      (fam.lo e ≠ a ∨ fam.hi e ≠ b) := by
  unfold Sstrict; rw [mem_filter, mem_contained]; unfold IsStrict; exact Iff.rfl
def containersS (a b : ℕ) (f : ι) : Finset ι :=
  (Sstrict fam a b).filter (fun g => fam.lo g ≤ fam.lo f ∧ fam.hi f ≤ fam.hi g)
lemma mem_containersS {a b : ℕ} {f g : ι} :
    g ∈ containersS fam a b f ↔
      ((g ∈ fam.E ∧ a ≤ fam.lo g ∧ fam.hi g ≤ b) ∧ (fam.lo g ≠ a ∨ fam.hi g ≠ b)) ∧
        fam.lo g ≤ fam.lo f ∧ fam.hi f ≤ fam.hi g := by
  unfold containersS; rw [mem_filter, mem_Sstrict]
lemma containersS_nonempty {a b : ℕ} {f : ι} (hf : f ∈ Sstrict fam a b) :
    (containersS fam a b f).Nonempty := by
  refine ⟨f, ?_⟩
  rw [mem_containersS]
  rw [mem_Sstrict] at hf
  exact ⟨hf, le_refl _, le_refl _⟩
open Classical in
/-- The strict root of `f`: widest strict containing edge (total; junk = `f` off `Sstrict`). -/
noncomputable def rootS (a b : ℕ) (f : ι) : ι :=
  if hf : f ∈ Sstrict fam a b then
    (Finset.exists_max_image (containersS fam a b f) (fun g => fam.hi g - fam.lo g)
      (containersS_nonempty fam hf)).choose
  else f
variable {a b : ℕ}
noncomputable def Roots (a b : ℕ) : Finset ι :=
  (Sstrict fam a b).filter (fun r => rootS fam a b r = r)
def topEdges (a b : ℕ) : Finset ι :=
  (contained fam a b).filter (fun e => fam.lo e = a ∧ fam.hi e = b)
end AbstractLaminar
namespace CriticalPortraits
open Finset
open scoped BigOperators
lemma critical_sameFiber {d m : ℕ} {S : Finset (ZMod (d * m))} (hS : IsCriticalSet d m S)
    {x y : ZMod (d * m)} (hx : x ∈ S) (hy : y ∈ S) : x.val % m = y.val % m := by
  obtain ⟨⟨r, hr, hfib⟩, _⟩ := hS; rw [hfib _ hx, hfib _ hy]
variable {d m : ℕ}
noncomputable def hostSet (P : Finset (Finset (ZMod (d * m)))) (x : ZMod (d * m))
    (hx : x ∈ T P) : Finset (ZMod (d*m)) := (mem_T.mp hx).choose
lemma hostSet_mem {P : Finset (Finset (ZMod (d * m)))} {x : ZMod (d * m)} (hx : x ∈ T P) :
    hostSet P x hx ∈ P := (mem_T.mp hx).choose_spec.1
lemma mem_eraseMin_hostSet {P : Finset (Finset (ZMod (d * m)))} {x : ZMod (d * m)} (hx : x ∈ T P) :
    x ∈ eraseMin (hostSet P x hx) := (mem_T.mp hx).choose_spec.2
lemma mem_hostSet {P : Finset (Finset (ZMod (d * m)))} {x : ZMod (d * m)} (hx : x ∈ T P) :
    x ∈ hostSet P x hx := eraseMin_subset _ (mem_eraseMin_hostSet hx)
def belowIn (S : Finset (ZMod (d * m))) (x : ZMod (d * m)) : Finset (ZMod (d * m)) :=
  S.filter (fun y => y.val < x.val)
lemma belowIn_nonempty [NeZero (d * m)] {S : Finset (ZMod (d * m))} (h : S.Nonempty)
    {x : ZMod (d * m)} (hx : x ∈ eraseMin S) : (belowIn S x).Nonempty := by
  refine ⟨minVal S h, ?_⟩
  rw [belowIn, mem_filter]
  refine ⟨minVal_mem S h, ?_⟩
  have hxS := eraseMin_subset S hx
  have hxne := ((mem_eraseMin S h x).mp hx).2
  rcases lt_or_eq_of_le (minVal_le S h x hxS) with hlt | heq
  · exact hlt
  · exact absurd (ZMod.val_injective _ heq).symm hxne
noncomputable def predIn [NeZero (d * m)] (P : Finset (Finset (ZMod (d * m)))) (x : ZMod (d * m))
    (hx : x ∈ T P) : ZMod (d*m) := by
  classical
  exact (Finset.exists_max_image (belowIn (hostSet P x hx) x) (fun y => y.val)
    (belowIn_nonempty ⟨x, mem_hostSet hx⟩ (mem_eraseMin_hostSet hx))).choose
lemma predIn_mem_belowIn [NeZero (d * m)] {P : Finset (Finset (ZMod (d * m)))} {x : ZMod (d * m)}
    (hx : x ∈ T P) : predIn P x hx ∈ belowIn (hostSet P x hx) x :=
  (Finset.exists_max_image (belowIn (hostSet P x hx) x) (fun y => y.val)
    (belowIn_nonempty ⟨x, mem_hostSet hx⟩ (mem_eraseMin_hostSet hx))).choose_spec.1
lemma predIn_max [NeZero (d * m)] {P : Finset (Finset (ZMod (d * m)))} {x : ZMod (d * m)}
    (hx : x ∈ T P) : ∀ y ∈ belowIn (hostSet P x hx) x, y.val ≤ (predIn P x hx).val :=
  (Finset.exists_max_image (belowIn (hostSet P x hx) x) (fun y => y.val)
    (belowIn_nonempty ⟨x, mem_hostSet hx⟩ (mem_eraseMin_hostSet hx))).choose_spec.2
lemma predIn_mem_host [NeZero (d * m)] {P : Finset (Finset (ZMod (d * m)))} {x : ZMod (d * m)}
    (hx : x ∈ T P) : predIn P x hx ∈ hostSet P x hx :=
  (mem_filter.mp (predIn_mem_belowIn hx)).1
lemma predIn_val_lt [NeZero (d * m)] {P : Finset (Finset (ZMod (d * m)))} {x : ZMod (d * m)}
    (hx : x ∈ T P) : (predIn P x hx).val < x.val :=
  (mem_filter.mp (predIn_mem_belowIn hx)).2
lemma hostSet_critical {P : Finset (Finset (ZMod (d * m)))} (hP : Portrait d m P) {x : ZMod (d * m)}
    (hx : x ∈ T P) : IsCriticalSet d m (hostSet P x hx) := hP.1 _ (hostSet_mem hx)
lemma predIn_sameFiber [NeZero (d * m)] {P : Finset (Finset (ZMod (d * m)))} (hP : Portrait d m P)
    {x : ZMod (d * m)} (hx : x ∈ T P) : (predIn P x hx).val % m = x.val % m :=
  critical_sameFiber (hostSet_critical hP hx) (predIn_mem_host hx) (mem_hostSet hx)
lemma predIn_level_lt (hd : 0 < d) (hm : 0 < m) {P : Finset (Finset (ZMod (d * m)))}
    (hP : Portrait d m P) {x : ZMod (d * m)} (hx : x ∈ T P) :
    haveI : NeZero (d*m) := ⟨by positivity⟩
    (predIn P x hx).val / m < x.val / m := by
  have : NeZero (d*m) := ⟨by positivity⟩
  have hsame := predIn_sameFiber hP hx
  have hvlt := predIn_val_lt hx
  rcases lt_or_eq_of_le ((val_le_iff_level_le_of_sameFiber hsame).mp hvlt.le) with hlt | heq
  · exact hlt
  · exact absurd (congrArg ZMod.val (level_injOn_fiber hsame heq)) (Nat.ne_of_lt hvlt)
lemma predIn_immediate [NeZero (d * m)] {P : Finset (Finset (ZMod (d * m)))} {x : ZMod (d * m)}
    (hx : x ∈ T P) {z : ZMod (d * m)} (hz : z ∈ hostSet P x hx)
    (h1 : (predIn P x hx).val < z.val) (h2 : z.val < x.val) : False := by
  have hzb : z ∈ belowIn (hostSet P x hx) x := by
    rw [belowIn, mem_filter]; exact ⟨hz, h2⟩
  have := predIn_max hx z hzb
  omega
lemma cross_false [NeZero (d * m)] {P : Finset (Finset (ZMod (d * m)))} (hP : Portrait d m P)
    {x y : ZMod (d * m)} (hx : x ∈ T P) (hy : y ∈ T P)
    (hhost : hostSet P x hx ≠ hostSet P y hy)
    (o1 : (predIn P x hx).val < (predIn P y hy).val)
    (o2 : (predIn P y hy).val < x.val)
    (o3 : x.val < y.val) : False := by
  have hL : Linked (hostSet P x hx) (hostSet P y hy) :=
    linked_of_lt (predIn_mem_host hx) (mem_hostSet hx) (predIn_mem_host hy) (mem_hostSet hy)
      o1 o2 o3
  exact (hP.2.2.1 _ (hostSet_mem hx) _ (hostSet_mem hy) hhost) hL
def hiV (x : ZMod (d * m)) : ℕ := x.val / m
def colV (x : ZMod (d * m)) : ℕ := x.val % m
noncomputable def loV [NeZero (d * m)] (P : Finset (Finset (ZMod (d * m))))
    (x : ZMod (d * m)) : ℕ :=
  if hx : x ∈ T P then (predIn P x hx).val / m else 0
lemma loV_eq [NeZero (d * m)] {P : Finset (Finset (ZMod (d * m)))} {x : ZMod (d * m)}
    (hx : x ∈ T P) :
    loV P x = (predIn P x hx).val / m := by
  unfold loV; rw [dif_pos hx]
lemma top_val_eq {x : ZMod (d * m)} : x.val = colV x + hiV x * m := by
  unfold colV hiV; have := Nat.div_add_mod' x.val m; omega
lemma pred_val_eq [NeZero (d * m)] {P : Finset (Finset (ZMod (d * m)))} (hP : Portrait d m P)
    {x : ZMod (d * m)} (hx : x ∈ T P) : (predIn P x hx).val = colV x + loV P x * m := by
  have hsame := predIn_sameFiber hP hx
  rw [loV_eq hx]
  unfold colV
  rw [← hsame]
  have := Nat.div_add_mod' (predIn P x hx).val m; omega
lemma no_alt [NeZero (d * m)] {P : Finset (Finset (ZMod (d * m)))} (hP : Portrait d m P)
    {x y : ZMod (d * m)} (hx : x ∈ T P) (hy : y ∈ T P)
    (o1 : (predIn P x hx).val < (predIn P y hy).val)
    (o2 : (predIn P y hy).val < x.val)
    (o3 : x.val < y.val) : False := by
  by_cases hhost : hostSet P x hx = hostSet P y hy
  · -- same host: predIn y lies strictly between predIn x and x, in host x
    apply predIn_immediate hx (z := predIn P y hy) ?_ o1 o2
    rw [hhost]; exact predIn_mem_host hy
  · exact cross_false hP hx hy hhost o1 o2 o3
lemma predEq_imp_sameHost {P : Finset (Finset (ZMod (d * m)))} (hP : Portrait d m P)
    {x y : ZMod (d * m)} (hx : x ∈ T P) (hy : y ∈ T P)
    [NeZero (d * m)] (hpe : predIn P x hx = predIn P y hy) :
    hostSet P x hx = hostSet P y hy := by
  by_contra hne
  have hdisj := hP.2.1 _ (hostSet_mem hx) _ (hostSet_mem hy) hne
  have hmemx : predIn P x hx ∈ hostSet P x hx := predIn_mem_host hx
  have hmemy : predIn P x hx ∈ hostSet P y hy := hpe ▸ predIn_mem_host hy
  exact (Finset.disjoint_left.mp hdisj hmemx) hmemy
lemma colV_lt_m (hm : 0 < m) (x : ZMod (d * m)) : colV x < m := Nat.mod_lt _ hm
lemma lemmaA [NeZero (d * m)] (hm : 0 < m)
    {P : Finset (Finset (ZMod (d * m)))} (hP : Portrait d m P)
    {e f : ZMod (d * m)} (he : e ∈ T P) (hf : f ∈ T P)
    (h1 : loV P e < loV P f) (h2 : loV P f < hiV e) (h3 : hiV e < hiV f) : False := by
  -- build the alternation px < py < e.val < f.val
  have hpe := pred_val_eq hP he
  have hpf := pred_val_eq hP hf
  have hte := top_val_eq (x := e)
  have htf := top_val_eq (x := f)
  have hce := colV_lt_m hm e
  have hcf := colV_lt_m hm f
  -- o1: predIn e .val < predIn f .val   (loV e < loV f)
  have o1 : (predIn P e he).val < (predIn P f hf).val := by
    rw [hpe, hpf]; have := sep_master (m := m) (p := colV e) (q := colV f) hce hcf h1; omega
  -- o2: predIn f .val < e.val   (loV f < hiV e)
  have o2 : (predIn P f hf).val < e.val := by
    rw [hpf, hte]; have := sep_master (m := m) (p := colV f) (q := colV e) hcf hce h2; omega
  -- o3: e.val < f.val   (hiV e < hiV f)
  have o3 : e.val < f.val := by
    rw [hte, htf]; have := sep_master (m := m) (p := colV e) (q := colV f) hce hcf h3; omega
  exact no_alt hP he hf o1 o2 o3
lemma lemmaB_seam [NeZero (d * m)] (hd : 0 < d) (hm : 0 < m)
    {P : Finset (Finset (ZMod (d * m)))} (hP : Portrait d m P)
    {e f : ZMod (d * m)} (he : e ∈ T P) (hf : f ∈ T P) (hseam : hiV e = loV P f) :
    colV e ≤ colV f := by
  by_contra hc
  rw [not_le] at hc  -- colV f < colV e
  have hpe := pred_val_eq hP he
  have hpf := pred_val_eq hP hf
  have hte := top_val_eq (x := e)
  have htf := top_val_eq (x := f)
  have hce := colV_lt_m hm e
  have hcf := colV_lt_m hm f
  have hlhe : loV P e < hiV e := by rw [loV_eq he]; exact predIn_level_lt hd hm hP he
  have hlhf : loV P f < hiV f := by rw [loV_eq hf]; exact predIn_level_lt hd hm hP hf
  -- o1: predIn e .val < predIn f .val
  have o1 : (predIn P e he).val < (predIn P f hf).val := by
    rw [hpe, hpf, ← hseam]
    have := sep_master (m := m) (p := colV e) (q := colV f) hce hcf hlhe
    omega
  -- o2: predIn f .val < e.val
  have o2 : (predIn P f hf).val < e.val := by
    rw [hpf, hte, ← hseam]; omega
  -- o3: e.val < f.val
  have o3 : e.val < f.val := by
    rw [hte, htf]
    have hef : hiV e < hiV f := by rw [hseam]; exact hlhf
    have := sep_master (m := m) (p := colV e) (q := colV f) hce hcf hef
    omega
  exact no_alt hP he hf o1 o2 o3
lemma lemmaB_right [NeZero (d * m)] (hd : 0 < d) (hm : 0 < m)
    {P : Finset (Finset (ZMod (d * m)))} (hP : Portrait d m P)
    {e f : ZMod (d * m)} (he : e ∈ T P) (hf : f ∈ T P)
    (htop : hiV e = hiV f) (hlo : loV P e < loV P f) : colV f < colV e := by
  by_contra hc
  rw [not_lt] at hc  -- colV e ≤ colV f
  have hpe := pred_val_eq hP he
  have hpf := pred_val_eq hP hf
  have hte := top_val_eq (x := e)
  have htf := top_val_eq (x := f)
  have hce := colV_lt_m hm e
  have hcf := colV_lt_m hm f
  have hlhf : loV P f < hiV f := by rw [loV_eq hf]; exact predIn_level_lt hd hm hP hf
  rcases lt_or_eq_of_le hc with hclt | hceq
  · -- colV e < colV f: alternation e,f
    have o1 : (predIn P e he).val < (predIn P f hf).val := by
      rw [hpe, hpf]
      have := sep_master (m := m) (p := colV e) (q := colV f) hce hcf hlo
      omega
    have o2 : (predIn P f hf).val < e.val := by
      rw [hpf, hte]
      have hlt : loV P f < hiV e := by rw [htop]; exact hlhf
      have := sep_master (m := m) (p := colV f) (q := colV e) hcf hce hlt
      omega
    have o3 : e.val < f.val := by
      rw [hte, htf, ← htop]; omega
    exact no_alt hP he hf o1 o2 o3
  · -- colV e = colV f ⇒ e = f ⇒ loV e = loV f, contra loV e < loV f
    have hval : e.val = f.val := by rw [hte, htf, htop, hceq]
    have : e = f := ZMod.val_injective _ hval
    rw [this] at hlo; omega
lemma lemmaB_left [NeZero (d * m)] (hd : 0 < d) (hm : 0 < m)
    {P : Finset (Finset (ZMod (d * m)))} (hP : Portrait d m P)
    {e f : ZMod (d * m)} (he : e ∈ T P) (hf : f ∈ T P)
    (hbot : loV P e = loV P f) (hhi : hiV f < hiV e) : colV e < colV f := by
  by_contra hc
  rw [not_lt] at hc  -- colV f ≤ colV e
  have hpe := pred_val_eq hP he
  have hpf := pred_val_eq hP hf
  have hte := top_val_eq (x := e)
  have htf := top_val_eq (x := f)
  have hce := colV_lt_m hm e
  have hcf := colV_lt_m hm f
  have hlhf : loV P f < hiV f := by rw [loV_eq hf]; exact predIn_level_lt hd hm hP hf
  rcases lt_or_eq_of_le hc with hclt | hceq
  · -- colV f < colV e: alternation f,e
    have o1 : (predIn P f hf).val < (predIn P e he).val := by
      rw [hpf, hpe, ← hbot]; omega
    have o2 : (predIn P e he).val < f.val := by
      rw [hpe, htf, hbot]
      have hlt : loV P f < hiV f := hlhf
      have := sep_master (m := m) (p := colV e) (q := colV f) hce hcf hlt
      omega
    have o3 : f.val < e.val := by
      rw [htf, hte]
      have := sep_master (m := m) (p := colV f) (q := colV e) hcf hce hhi
      omega
    exact no_alt hP hf he o1 o2 o3
  · -- colV f = colV e ⇒ predIn e = predIn f ⇒ same host ⇒ f between p and e ⇒ immediacy
    have hpv : (predIn P e he).val = (predIn P f hf).val := by rw [hpe, hpf, hbot, hceq]
    have hpeq : predIn P e he = predIn P f hf := ZMod.val_injective _ hpv
    have hhost := predEq_imp_sameHost hP he hf hpeq
    -- f ∈ hostSet e
    have hfmem : f ∈ hostSet P e he := by rw [hhost]; exact mem_hostSet hf
    -- p.val < f.val < e.val
    have hlt1 : (predIn P e he).val < f.val := by
      rw [hpe, htf, hbot]
      have := sep_master (m := m) (p := colV e) (q := colV f) hce hcf hlhf
      omega
    have hlt2 : f.val < e.val := by
      rw [htf, hte]
      have := sep_master (m := m) (p := colV f) (q := colV e) hcf hce hhi
      omega
    exact predIn_immediate he hfmem hlt1 hlt2
lemma edge_inj [NeZero (d * m)] (hd : 0 < d) (hm : 0 < m)
    {P : Finset (Finset (ZMod (d * m)))} (hP : Portrait d m P)
    {e f : ZMod (d * m)} (he : e ∈ T P) (hf : f ∈ T P)
    (hlo : loV P e = loV P f) (hhi : hiV e = hiV f) : e = f := by
  by_contra hne
  have hte := top_val_eq (x := e)
  have htf := top_val_eq (x := f)
  have hce := colV_lt_m hm e
  have hcf := colV_lt_m hm f
  have hpe := pred_val_eq hP he
  have hpf := pred_val_eq hP hf
  have hlhe : loV P e < hiV e := by rw [loV_eq he]; exact predIn_level_lt hd hm hP he
  -- colV e ≠ colV f (else same val ⇒ equal)
  have hcne : colV e ≠ colV f := by
    intro h
    exact hne (ZMod.val_injective _ (by rw [hte, htf, hhi, h]))
  rcases Nat.lt_or_ge (colV e) (colV f) with hclt | hcge
  · -- alternation e,f
    have o1 : (predIn P e he).val < (predIn P f hf).val := by rw [hpe, hpf, hlo]; omega
    have o2 : (predIn P f hf).val < e.val := by
      rw [hpf, hte, ← hlo]
      have := sep_master (m := m) (p := colV f) (q := colV e) hcf hce hlhe
      omega
    have o3 : e.val < f.val := by rw [hte, htf, ← hhi]; omega
    exact no_alt hP he hf o1 o2 o3
  · -- colV f < colV e (since ≠): alternation f,e
    have hclt : colV f < colV e := lt_of_le_of_ne hcge (fun h => hcne h.symm)
    have hlhf : loV P f < hiV f := by rw [loV_eq hf]; exact predIn_level_lt hd hm hP hf
    have o1 : (predIn P f hf).val < (predIn P e he).val := by rw [hpf, hpe, ← hlo]; omega
    have o2 : (predIn P e he).val < f.val := by
      rw [hpe, htf, hlo]
      have := sep_master (m := m) (p := colV e) (q := colV f) hce hcf hlhf
      omega
    have o3 : f.val < e.val := by rw [htf, hte, hhi]; omega
    exact no_alt hP hf he o1 o2 o3
noncomputable def survivorFamily [NeZero (d * m)] (hd : 0 < d) (hm : 0 < m)
    {P : Finset (Finset (ZMod (d * m)))} (hP : Portrait d m P) :
    AbstractLaminar.Family (ZMod (d*m)) where
  E := T P
  lo := loV P
  hi := hiV
  col := colV
  lh := fun e he => by rw [loV_eq he]; exact predIn_level_lt hd hm hP he
  inj := fun e he f hf hlo hhi => edge_inj hd hm hP he hf hlo hhi
  laminar := fun e he f hf => fun ⟨h1, h2, h3⟩ => lemmaA hm hP he hf h1 h2 h3
  bRight := fun e he f hf htop hlo => lemmaB_right hd hm hP he hf htop hlo
  bLeft := fun e he f hf hbot hhi => lemmaB_left hd hm hP he hf hbot hhi
  bSeam := fun e he f hf hseam => lemmaB_seam hd hm hP he hf hseam
end CriticalPortraits



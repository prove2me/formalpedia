-- Prove2me | Definitions.Def_KServer_chunk_cond
-- name    : KServer_chunk_cond
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-09-01T10:32:37.027652+00:00
-- url     : https://prove2.me/theorems/38b73873-aaa1-4d8f-9ea8-4d3c349964af
-- title:
--   Conditional expectations and the Doob total of a chunk system
-- statement:
--   The finite conditional-expectation toolkit over a chunk system with online escapes: filtration atoms (encoded by the history function), strictly positive atom masses, the atomwise conditional expectation with its measurability, linearity, monotonicity, pointwise bounds, the defining averaging identity, the tower property (atom-sum, pointwise, and total-expectation forms), the past/future size split of the total mass, and the **Doob martingale of the total size** $M_h = \mathbb{E}[\sum_i c_i \mid \mathcal F_h]$ together with the **Doob jump bound** predicate $|M_{h+1} - M_h| \le jb$ — the regularity invariant carried through the BCR induction that pins down-trigger overshoots in the chunk-combining lemma.
-- source:
--   S. Bubeck, C. Coester, Y. Rabani, 'The randomized k-server conjecture is false!', STOC 2023, Section 5 (Lemma 10 machinery), repaired form.

import Mathlib
import Definitions.Def_KServer_evader
import Definitions.Def_KServer_evader_bail
import Definitions.Def_KServer_chunk_system_b

set_option linter.unreachableTactic false
set_option linter.unusedTactic false

namespace KServer

namespace ChunkSystemB

variable {X : Type*} [MetricSpace X] {s t : X} {cLo cHi total price : ℝ} {mLo : ℕ}
variable (C : ChunkSystemB X s t cLo cHi total price mLo)

/-- The atom of the time-`h` filtration that contains the outcome `ω`. -/
def atom (h : ℕ) (ω : C.Ω) : Finset C.Ω :=
  Finset.univ.filter fun ω' => C.hist h ω' = C.hist h ω

theorem mem_atom {h : ℕ} {ω ω' : C.Ω} :
    ω' ∈ C.atom h ω ↔ C.hist h ω' = C.hist h ω := by
  simp [atom]

theorem mem_atom_self (h : ℕ) (ω : C.Ω) : ω ∈ C.atom h ω := by
  simp [atom]

theorem atom_eq_of_hist_eq {h : ℕ} {ω ω' : C.Ω}
    (hh : C.hist h ω' = C.hist h ω) : C.atom h ω' = C.atom h ω := by
  ext ω''
  simp only [mem_atom, hh]

theorem atom_eq_of_mem {h : ℕ} {ω ω' : C.Ω} (hmem : ω' ∈ C.atom h ω) :
    C.atom h ω' = C.atom h ω :=
  C.atom_eq_of_hist_eq (C.mem_atom.mp hmem)

/-- Refinement: atoms of a later time are contained in atoms of an earlier time. -/
theorem atom_subset {h h' : ℕ} (hle : h ≤ h') (ω : C.Ω) :
    C.atom h' ω ⊆ C.atom h ω := by
  intro ω' hm
  rw [mem_atom] at hm ⊢
  exact C.href h h' hle ω' ω hm

/-- The probability mass of a set of outcomes. -/
def mass (A : Finset C.Ω) : ℝ := ∑ ω ∈ A, C.P ω

theorem mass_nonneg (A : Finset C.Ω) : 0 ≤ C.mass A :=
  Finset.sum_nonneg fun ω _ => le_of_lt (C.hP ω)

theorem mass_atom_pos (h : ℕ) (ω : C.Ω) : 0 < C.mass (C.atom h ω) :=
  Finset.sum_pos' (fun ω' _ => le_of_lt (C.hP ω'))
    ⟨ω, C.mem_atom_self h ω, C.hP ω⟩

/-- Conditional expectation of `f` given the time-`h` filtration, evaluated
at the outcome `ω`: the `P`-average of `f` over the atom of `ω`. -/
noncomputable def condExp (f : C.Ω → ℝ) (h : ℕ) (ω : C.Ω) : ℝ :=
  (∑ ω' ∈ C.atom h ω, C.P ω' * f ω') / C.mass (C.atom h ω)

/-- The conditional expectation is measurable: it depends only on the atom. -/
theorem condExp_congr (f : C.Ω → ℝ) {h : ℕ} {ω ω' : C.Ω}
    (hh : C.hist h ω' = C.hist h ω) :
    C.condExp f h ω' = C.condExp f h ω := by
  unfold condExp
  rw [C.atom_eq_of_hist_eq hh]

theorem condExp_const (c : ℝ) (h : ℕ) (ω : C.Ω) :
    C.condExp (fun _ => c) h ω = c := by
  have hmne : C.mass (C.atom h ω) ≠ 0 := ne_of_gt (C.mass_atom_pos h ω)
  unfold condExp
  rw [← Finset.sum_mul]
  show C.mass (C.atom h ω) * c / C.mass (C.atom h ω) = c
  rw [mul_div_cancel_left₀ c hmne]

theorem condExp_add (f g : C.Ω → ℝ) (h : ℕ) (ω : C.Ω) :
    C.condExp (fun ω' => f ω' + g ω') h ω = C.condExp f h ω + C.condExp g h ω := by
  unfold condExp
  rw [← add_div]
  congr 1
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun ω' _ => ?_
  show C.P ω' * (f ω' + g ω') = _
  ring

/-- If `f = g` on the atom of `ω`, the conditional expectations agree. -/
theorem condExp_congr_fun {f g : C.Ω → ℝ} {h : ℕ} {ω : C.Ω}
    (hfg : ∀ ω' ∈ C.atom h ω, f ω' = g ω') :
    C.condExp f h ω = C.condExp g h ω := by
  unfold condExp
  congr 1
  exact Finset.sum_congr rfl fun ω' hm => by rw [hfg ω' hm]

/-- A pointwise lower bound on the atom bounds the conditional expectation
from below. -/
theorem le_condExp {f : C.Ω → ℝ} {h : ℕ} {ω : C.Ω} {a : ℝ}
    (hf : ∀ ω' ∈ C.atom h ω, a ≤ f ω') : a ≤ C.condExp f h ω := by
  have hm := C.mass_atom_pos h ω
  unfold condExp
  rw [le_div_iff₀ hm]
  calc a * C.mass (C.atom h ω) = ∑ ω' ∈ C.atom h ω, a * C.P ω' := by
        unfold mass; rw [Finset.mul_sum]
    _ ≤ ∑ ω' ∈ C.atom h ω, C.P ω' * f ω' :=
        Finset.sum_le_sum fun ω' hm' => by nlinarith [C.hP ω', hf ω' hm']

/-- A pointwise upper bound on the atom bounds the conditional expectation
from above. -/
theorem condExp_le {f : C.Ω → ℝ} {h : ℕ} {ω : C.Ω} {b : ℝ}
    (hf : ∀ ω' ∈ C.atom h ω, f ω' ≤ b) : C.condExp f h ω ≤ b := by
  have hm := C.mass_atom_pos h ω
  unfold condExp
  rw [div_le_iff₀ hm]
  calc ∑ ω' ∈ C.atom h ω, C.P ω' * f ω'
      ≤ ∑ ω' ∈ C.atom h ω, b * C.P ω' :=
        Finset.sum_le_sum fun ω' hm' => by nlinarith [C.hP ω', hf ω' hm']
    _ = b * C.mass (C.atom h ω) := by unfold mass; rw [Finset.mul_sum]

theorem condExp_mono {f g : C.Ω → ℝ} (h : ℕ) (ω : C.Ω)
    (hfg : ∀ ω' ∈ C.atom h ω, f ω' ≤ g ω') :
    C.condExp f h ω ≤ C.condExp g h ω := by
  have hm := C.mass_atom_pos h ω
  have hnum : (∑ ω' ∈ C.atom h ω, C.P ω' * f ω')
      ≤ ∑ ω' ∈ C.atom h ω, C.P ω' * g ω' :=
    Finset.sum_le_sum fun ω' hm' =>
      mul_le_mul_of_nonneg_left (hfg ω' hm') (le_of_lt (C.hP ω'))
  unfold condExp
  rw [div_le_iff₀ hm, div_mul_cancel₀ _ (ne_of_gt hm)]
  exact hnum

/-- Averaging over one atom recovers the weighted sum: the defining identity
of the conditional expectation, in product form. -/
theorem sum_atom_mul_condExp (f : C.Ω → ℝ) (h : ℕ) (ω₀ : C.Ω) :
    ∑ ω ∈ C.atom h ω₀, C.P ω * C.condExp f h ω
      = ∑ ω ∈ C.atom h ω₀, C.P ω * f ω := by
  have hmne : C.mass (C.atom h ω₀) ≠ 0 := ne_of_gt (C.mass_atom_pos h ω₀)
  have hconst : ∀ ω ∈ C.atom h ω₀, C.condExp f h ω = C.condExp f h ω₀ :=
    fun ω hm => C.condExp_congr f (C.mem_atom.mp hm)
  rw [Finset.sum_congr rfl fun ω hm => by rw [hconst ω hm], ← Finset.sum_mul]
  show C.mass (C.atom h ω₀) * C.condExp f h ω₀ = _
  rw [mul_comm]
  unfold condExp
  rw [div_mul_cancel₀ _ hmne]

/-- The tower property in sum form: summing `P · condExp f h'` over a
coarser atom (at time `h ≤ h'`) recovers the weighted sum of `f`. -/
theorem sum_atom_mul_condExp_of_le (f : C.Ω → ℝ) {h h' : ℕ} (hle : h ≤ h')
    (ω₀ : C.Ω) :
    ∑ ω ∈ C.atom h ω₀, C.P ω * C.condExp f h' ω
      = ∑ ω ∈ C.atom h ω₀, C.P ω * f ω := by
  classical
  have hfib := Finset.sum_fiberwise_of_maps_to
    (s := C.atom h ω₀) (t := (C.atom h ω₀).image (C.hist h'))
    (g := C.hist h') (fun ω hm => Finset.mem_image_of_mem _ hm)
    (fun ω => C.P ω * C.condExp f h' ω)
  have hfib' := Finset.sum_fiberwise_of_maps_to
    (s := C.atom h ω₀) (t := (C.atom h ω₀).image (C.hist h'))
    (g := C.hist h') (fun ω hm => Finset.mem_image_of_mem _ hm)
    (fun ω => C.P ω * f ω)
  rw [← hfib, ← hfib']
  refine Finset.sum_congr rfl fun b hb => ?_
  obtain ⟨ω₁, hω₁, hb1⟩ := Finset.mem_image.mp hb
  have hfiber : (C.atom h ω₀).filter (fun ω => C.hist h' ω = b) = C.atom h' ω₁ := by
    ext ω
    simp only [Finset.mem_filter, mem_atom]
    constructor
    · rintro ⟨_, hωb⟩
      rw [hωb, hb1]
    · intro hω
      exact ⟨(C.href h h' hle ω ω₁ hω).trans (C.mem_atom.mp hω₁), by rw [hω, hb1]⟩
  rw [hfiber]
  exact C.sum_atom_mul_condExp f h' ω₁

/-- The tower property, pointwise form. -/
theorem condExp_condExp {f : C.Ω → ℝ} {h h' : ℕ} (hle : h ≤ h') (ω : C.Ω) :
    C.condExp (C.condExp f h') h ω = C.condExp f h ω := by
  show (∑ ω' ∈ C.atom h ω, C.P ω' * C.condExp f h' ω') / C.mass (C.atom h ω)
      = C.condExp f h ω
  rw [C.sum_atom_mul_condExp_of_le f hle ω]
  rfl

/-- Total expectation: the `P`-weighted sum of a conditional expectation
equals the `P`-weighted sum of the function. -/
theorem sum_mul_condExp (f : C.Ω → ℝ) (h : ℕ) :
    ∑ ω, C.P ω * C.condExp f h ω = ∑ ω, C.P ω * f ω := by
  classical
  have hfib := Finset.sum_fiberwise_of_maps_to
    (s := (Finset.univ : Finset C.Ω)) (t := Finset.univ.image (C.hist h))
    (g := C.hist h) (fun ω hm => Finset.mem_image_of_mem _ hm)
    (fun ω => C.P ω * C.condExp f h ω)
  have hfib' := Finset.sum_fiberwise_of_maps_to
    (s := (Finset.univ : Finset C.Ω)) (t := Finset.univ.image (C.hist h))
    (g := C.hist h) (fun ω hm => Finset.mem_image_of_mem _ hm)
    (fun ω => C.P ω * f ω)
  rw [← hfib, ← hfib']
  refine Finset.sum_congr rfl fun b hb => ?_
  obtain ⟨ω₁, _, hb1⟩ := Finset.mem_image.mp hb
  have hfiber : Finset.univ.filter (fun ω => C.hist h ω = b) = C.atom h ω₁ := by
    ext ω
    simp only [Finset.mem_filter, mem_atom, Finset.mem_univ, true_and]
    rw [hb1]
  rw [hfiber]
  exact C.sum_atom_mul_condExp f h ω₁

/-- The sum of the sizes of all chunks of an outcome. -/
def totalSize (ω : C.Ω) : ℝ := ∑ i, C.size ω i

/-- The sum of the sizes of the chunks from index `h` on. -/
def futureSize (h : ℕ) (ω : C.Ω) : ℝ :=
  ∑ i ∈ Finset.univ.filter (fun i : Fin C.m => h ≤ i.val), C.size ω i

/-- The sum of the sizes of the chunks before index `h`. -/
def pastSize (h : ℕ) (ω : C.Ω) : ℝ :=
  ∑ i ∈ Finset.univ.filter (fun i : Fin C.m => i.val < h), C.size ω i

theorem pastSize_add_futureSize (h : ℕ) (ω : C.Ω) :
    C.pastSize h ω + C.futureSize h ω = C.totalSize ω := by
  have hsplit : C.futureSize h ω
      = ∑ i ∈ Finset.univ.filter (fun i : Fin C.m => ¬ i.val < h), C.size ω i := by
    unfold futureSize
    congr 1
    ext i
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    omega
  rw [hsplit]
  unfold pastSize totalSize
  exact Finset.sum_filter_add_sum_filter_not Finset.univ _ _

/-- The past sizes are known at time `h`: `pastSize h` is constant on
time-`h` atoms. -/
theorem pastSize_congr {h : ℕ} {ω ω' : C.Ω} (hh : C.hist h ω' = C.hist h ω) :
    C.pastSize h ω' = C.pastSize h ω := by
  unfold pastSize
  refine Finset.sum_congr rfl fun i hi => ?_
  simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hi
  exact C.hsmeas i ω' ω (C.href i h (by omega) ω' ω hh)

/-- The **Doob martingale of the total size**: the conditional expectation of
the total size given the time-`h` filtration. -/
noncomputable def doobTotal (h : ℕ) (ω : C.Ω) : ℝ := C.condExp C.totalSize h ω

/-- The **conditional future mass** at time `h`. -/
noncomputable def condFuture (h : ℕ) (ω : C.Ω) : ℝ := C.condExp (C.futureSize h) h ω

/-- The Doob total splits as the (known) past mass plus the conditional
future mass. -/
theorem doobTotal_eq_past_add_condFuture (h : ℕ) (ω : C.Ω) :
    C.doobTotal h ω = C.pastSize h ω + C.condFuture h ω := by
  unfold doobTotal condFuture
  rw [show C.totalSize = fun ω' => C.pastSize h ω' + C.futureSize h ω' from
    funext fun ω' => (C.pastSize_add_futureSize h ω').symm]
  rw [C.condExp_add]
  congr 1
  rw [show C.condExp (C.pastSize h) h ω
      = C.condExp (fun _ => C.pastSize h ω) h ω from
    C.condExp_congr_fun fun ω' hm => C.pastSize_congr (C.mem_atom.mp hm)]
  exact C.condExp_const _ h ω

/-- A **Doob jump bound** for a chunk system: every one-step jump of the Doob
martingale of the total size is at most `jb` in absolute value. This is the
regularity hypothesis `(I5)` carried through the BCR induction: revealing one
more chunk of history moves the conditional expectation of the total mass by
at most `jb`. -/
def DoobJumpBound (jb : ℝ) : Prop :=
  ∀ (h : ℕ) (ω : C.Ω), |C.doobTotal (h + 1) ω - C.doobTotal h ω| ≤ jb

end ChunkSystemB

end KServer



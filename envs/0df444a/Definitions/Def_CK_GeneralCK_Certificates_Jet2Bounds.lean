-- Prove2me | Definitions.Def_CK_GeneralCK_Certificates_Jet2Bounds
-- name    : CK_GeneralCK_Certificates_Jet2Bounds
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-09-27T22:25:10.841525+00:00
-- url     : https://prove2.me/theorems/83d65b6f-09a1-4226-9d2f-4197ee7d72b6
-- title:
--   Courtade–Kumar proof module `GeneralCK.Certificates.Jet2Bounds` (transplant)
-- statement:
--   Verbatim transplant of the Lean module `GeneralCK.Certificates.Jet2Bounds` of the machine-checked proof of the general Courtade–Kumar theorem (the most informative Boolean function conjecture), so that the complete proof can be verified on this platform.
--
--   It is the original source with only two mechanical changes. Imports of project modules are redirected to their transplanted bundles `Definitions.Def_CK_*`. Declarations that already exist in earlier platform definition bundles of this mission are removed, and those bundles are imported instead, so every constant keeps a single platform identity.
--
--   The module contains both definitions and the lemmas proved alongside them in the source. They are kept together so the transplant stays faithful and every proof is re-checked by the server.
--
--   Source: Z. Chen, A. Gohari, A. Javanmard, H. Lin, V. Mirrokni, C. Nair, D. P. Woodruff, *A Proof of the Most Informative Boolean Function Conjecture*, arXiv:2609.24931 (2026). Lean development: https://github.com/dpwoodru/general-courtade-kumar-lean (Apache-2.0), module `GeneralCK.Certificates.Jet2Bounds` from release v1.0 (`sources_v3.tar.zst`).
-- source:
--   arXiv:2609.24931; https://github.com/dpwoodru/general-courtade-kumar-lean release v1.0, module GeneralCK.Certificates.Jet2Bounds (browse copy where available: https://github.com/dpwoodru/general-courtade-kumar-lean/blob/04b6fc3f75b10c3c43702a883ddf888b0608a9a0/browse/GeneralCK/Certificates/Jet2Bounds.lean)

import Definitions.Def_CK_GeneralCK_Certificates_Jet2Composition
import Definitions.Def_CK_GeneralCK_Certificates_ReflectionBounds
import Definitions.Def_CK_GeneralCK_Certificates_TaylorBounds
import Definitions.Def_GeneralCK_RB2_checker_semantics_v2

namespace GeneralCK.Certificates.JetBounds






namespace Interval


def point (x : ℝ) : Interval := ⟨x,x⟩
def add (i j : Interval) : Interval := ⟨i.lo+j.lo,i.hi+j.hi⟩
def neg (i : Interval) : Interval := ⟨-i.hi,-i.lo⟩
def sub (i j : Interval) : Interval := i.add j.neg
noncomputable def mul (i j : Interval) : Interval :=
  ⟨min (min (i.lo*j.lo) (i.lo*j.hi)) (min (i.hi*j.lo) (i.hi*j.hi)),
   max (max (i.lo*j.lo) (i.lo*j.hi)) (max (i.hi*j.lo) (i.hi*j.hi))⟩
noncomputable def inv (i : Interval) : Interval := ⟨i.hi⁻¹,i.lo⁻¹⟩
noncomputable def div (i j : Interval) : Interval := i.mul j.inv
noncomputable def sq (i : Interval) : Interval := i.mul i
noncomputable def cube (i : Interval) : Interval := i.sq.mul i

theorem contains_point (x : ℝ) : (point x).Contains x := ⟨le_rfl,le_rfl⟩

theorem Contains.add {i j : Interval} {x y : ℝ} (hx : i.Contains x) (hy : j.Contains y) :
    (i.add j).Contains (x+y) := ⟨add_le_add hx.1 hy.1,add_le_add hx.2 hy.2⟩

theorem Contains.neg {i : Interval} {x : ℝ} (hx : i.Contains x) :
    i.neg.Contains (-x) := ⟨neg_le_neg hx.2,neg_le_neg hx.1⟩

theorem Contains.sub {i j : Interval} {x y : ℝ} (hx : i.Contains x) (hy : j.Contains y) :
    (i.sub j).Contains (x-y) := hx.add hy.neg

theorem Contains.mul {i j : Interval} {x y : ℝ} (hx : i.Contains x) (hy : j.Contains y) :
    (i.mul j).Contains (x*y) := by
  apply Reflection.bounds_mul hx hy <;> simp [Interval.mul]

theorem Contains.inv {i : Interval} {x : ℝ} (hx : i.Contains x) (hi : 0 < i.lo) :
    i.inv.Contains x⁻¹ :=
  Reflection.bounds_inv hx hi (by simp [Interval.inv,one_div]) (by simp [Interval.inv,one_div])

theorem Contains.div {i j : Interval} {x y : ℝ} (hx : i.Contains x) (hy : j.Contains y)
    (hj : 0 < j.lo) : (i.div j).Contains (x/y) := by
  simpa only [Interval.div,div_eq_mul_inv] using hx.mul (hy.inv hj)

theorem Contains.sq {i : Interval} {x : ℝ} (hx : i.Contains x) : i.sq.Contains (x^2) := by
  simpa only [Interval.sq,pow_two] using hx.mul hx

theorem Contains.cube {i : Interval} {x : ℝ} (hx : i.Contains x) : i.cube.Contains (x^3) := by
  simpa only [Interval.cube,pow_succ,pow_zero,one_mul] using hx.sq.mul hx

theorem Contains.log {i j : Interval} {x : ℝ} (hx : i.Contains x) (hi : 0 < i.lo)
    (hl : j.lo ≤ Real.log i.lo) (hu : Real.log i.hi ≤ j.hi) : j.Contains (Real.log x) :=
  Reflection.bounds_log hx hi hl hu

theorem Contains.widen {i j : Interval} {x : ℝ} (hx : i.Contains x)
    (hl : j.lo ≤ i.lo) (hu : i.hi ≤ j.hi) : j.Contains x :=
  Reflection.bounds_widen hx hl hu

end Interval






namespace JetEnclosure

def Contains (b : JetEnclosure) (j : Jet2) (t : ℝ) : Prop :=
  b.value.Contains (j.value t) ∧ b.first.Contains (j.first t) ∧ b.second.Contains (j.second t)

def const (c : ℝ) : JetEnclosure := ⟨.point c,.point 0,.point 0⟩
def variableJet (i : Interval) : JetEnclosure := ⟨i,.point 1,.point 0⟩
def add (b c : JetEnclosure) : JetEnclosure :=
  ⟨b.value.add c.value,b.first.add c.first,b.second.add c.second⟩
def neg (b : JetEnclosure) : JetEnclosure := ⟨b.value.neg,b.first.neg,b.second.neg⟩
noncomputable def mul (b c : JetEnclosure) : JetEnclosure :=
  ⟨b.value.mul c.value,
   (b.first.mul c.value).add (b.value.mul c.first),
   ((b.second.mul c.value).add (((Interval.point 2).mul b.first).mul c.first)).add
     (b.value.mul c.second)⟩

/-- Positive value bounds are required by the propagation theorem. -/
noncomputable def inv (b : JetEnclosure) : JetEnclosure :=
  let r := b.value.inv
  ⟨r,b.first.neg.mul r.sq,
   (((Interval.point 2).mul b.first.sq).mul r.cube).sub (b.second.mul r.sq)⟩

/-- The logarithm value interval is supplied by a checked endpoint enclosure. -/
noncomputable def log (b : JetEnclosure) (out : Interval) : JetEnclosure :=
  let r := b.value.inv
  ⟨out,b.first.mul r,(b.second.mul r).sub (b.first.sq.mul r.sq)⟩

/-- `b` encloses the outer jet at the value of the inner jet. -/
noncomputable def comp (b c : JetEnclosure) : JetEnclosure :=
  ⟨b.value,b.first.mul c.first,(b.second.mul c.first.sq).add (b.first.mul c.second)⟩

theorem contains_const (c t : ℝ) : (const c).Contains (Jet2.const c) t :=
  ⟨Interval.contains_point _,Interval.contains_point _,Interval.contains_point _⟩

theorem contains_variable {i : Interval} {t : ℝ} (ht : i.Contains t) :
    (variableJet i).Contains Jet2.variableJet t :=
  ⟨ht,Interval.contains_point _,Interval.contains_point _⟩

theorem Contains.add {b c : JetEnclosure} {j k : Jet2} {t : ℝ}
    (hj : b.Contains j t) (hk : c.Contains k t) : (b.add c).Contains (j.add k) t :=
  ⟨hj.1.add hk.1,hj.2.1.add hk.2.1,hj.2.2.add hk.2.2⟩

theorem Contains.neg {b : JetEnclosure} {j : Jet2} {t : ℝ} (hj : b.Contains j t) :
    b.neg.Contains j.neg t := ⟨hj.1.neg,hj.2.1.neg,hj.2.2.neg⟩

theorem Contains.mul {b c : JetEnclosure} {j k : Jet2} {t : ℝ}
    (hj : b.Contains j t) (hk : c.Contains k t) : (b.mul c).Contains (j.mul k) t :=
  ⟨hj.1.mul hk.1,(hj.2.1.mul hk.1).add (hj.1.mul hk.2.1),
    ((hj.2.2.mul hk.1).add (((Interval.contains_point 2).mul hj.2.1).mul hk.2.1)).add
      (hj.1.mul hk.2.2)⟩

theorem Contains.inv {b : JetEnclosure} {j : Jet2} {t : ℝ}
    (hj : b.Contains j t) (hb : 0 < b.value.lo) : b.inv.Contains j.inv t := by
  have hr := hj.1.inv hb
  refine ⟨hr,?_,?_⟩
  · simpa only [JetEnclosure.inv,Jet2.inv,div_eq_mul_inv,inv_pow] using hj.2.1.neg.mul hr.sq
  · simpa only [JetEnclosure.inv,Jet2.inv,div_eq_mul_inv,inv_pow] using
      (((Interval.contains_point 2).mul hj.2.1.sq).mul hr.cube).sub (hj.2.2.mul hr.sq)

theorem Contains.log {b : JetEnclosure} {out : Interval} {j : Jet2} {t : ℝ}
    (hj : b.Contains j t) (hb : 0 < b.value.lo)
    (hl : out.lo ≤ Real.log b.value.lo) (hu : Real.log b.value.hi ≤ out.hi) :
    (b.log out).Contains j.log t := by
  have hr := hj.1.inv hb
  refine ⟨hj.1.log hb hl hu,?_,?_⟩
  · simpa only [JetEnclosure.log,Jet2.log,div_eq_mul_inv] using hj.2.1.mul hr
  · simpa only [JetEnclosure.log,Jet2.log,div_eq_mul_inv,inv_pow] using (hj.2.2.mul hr).sub (hj.2.1.sq.mul hr.sq)

theorem Contains.comp {b c : JetEnclosure} {j k : Jet2} {t : ℝ}
    (hj : b.Contains j (k.value t)) (hk : c.Contains k t) :
    (b.comp c).Contains (j.comp k) t :=
  ⟨hj.1,hj.2.1.mul hk.2.1,(hj.2.2.mul hk.2.1.sq).add (hj.2.1.mul hk.2.2)⟩

theorem Contains.widen {b c : JetEnclosure} {j : Jet2} {t : ℝ} (hj : b.Contains j t)
    (hv : c.value.lo ≤ b.value.lo ∧ b.value.hi ≤ c.value.hi)
    (hf : c.first.lo ≤ b.first.lo ∧ b.first.hi ≤ c.first.hi)
    (hs : c.second.lo ≤ b.second.lo ∧ b.second.hi ≤ c.second.hi) : c.Contains j t :=
  ⟨hj.1.widen hv.1 hv.2,hj.2.1.widen hf.1 hf.2,hj.2.2.widen hs.1 hs.2⟩

def ContainsOn (b : JetEnclosure) (j : Jet2) (s : Set ℝ) : Prop := ∀ t ∈ s, b.Contains j t

theorem containsOn_const (c : ℝ) (s : Set ℝ) : (const c).ContainsOn (Jet2.const c) s :=
  fun t _ => contains_const c t

theorem ContainsOn.add {b c : JetEnclosure} {j k : Jet2} {s : Set ℝ}
    (hj : b.ContainsOn j s) (hk : c.ContainsOn k s) : (b.add c).ContainsOn (j.add k) s :=
  fun t ht => (hj t ht).add (hk t ht)

theorem ContainsOn.neg {b : JetEnclosure} {j : Jet2} {s : Set ℝ}
    (hj : b.ContainsOn j s) : b.neg.ContainsOn j.neg s := fun t ht => (hj t ht).neg

theorem ContainsOn.mul {b c : JetEnclosure} {j k : Jet2} {s : Set ℝ}
    (hj : b.ContainsOn j s) (hk : c.ContainsOn k s) : (b.mul c).ContainsOn (j.mul k) s :=
  fun t ht => (hj t ht).mul (hk t ht)

theorem ContainsOn.inv {b : JetEnclosure} {j : Jet2} {s : Set ℝ}
    (hj : b.ContainsOn j s) (hb : 0 < b.value.lo) : b.inv.ContainsOn j.inv s :=
  fun t ht => (hj t ht).inv hb

theorem ContainsOn.log {b : JetEnclosure} {out : Interval} {j : Jet2} {s : Set ℝ}
    (hj : b.ContainsOn j s) (hb : 0 < b.value.lo)
    (hl : out.lo ≤ Real.log b.value.lo) (hu : Real.log b.value.hi ≤ out.hi) :
    (b.log out).ContainsOn j.log s := fun t ht => (hj t ht).log hb hl hu

theorem ContainsOn.comp {b c : JetEnclosure} {j k : Jet2} {s u : Set ℝ}
    (hj : b.ContainsOn j u) (hk : c.ContainsOn k s) (hmap : Set.MapsTo k.value s u) :
    (b.comp c).ContainsOn (j.comp k) s :=
  fun t ht => (hj (k.value t) (hmap ht)).comp (hk t ht)

/-- A uniform enclosure and sound derivative chain give a checked Taylor lower bound. -/
theorem taylor_lower {b : JetEnclosure} {j : Jet2}
    (hj : j.SoundOn (Set.Icc (0:ℝ) 1)) (hb : b.ContainsOn j (Set.Icc (0:ℝ) 1)) :
    b.value.lo+b.first.lo+b.second.lo/2 ≤ j.value 1 := by
  have h0 := hb 0 (by norm_num)
  have ht := taylor_lower_from_enclosures (fun t ht => (hj t ht).1)
    (fun t ht => (hj t ⟨ht.1.le,ht.2.le⟩).2) h0.1.1
    (show -(-b.first.lo) ≤ j.first 0 by simpa using h0.2.1.1)
    (M := -b.second.lo) (fun t ht => by simpa using (hb t ⟨ht.1.le,ht.2.le⟩).2.2.1)
  linarith

theorem value_pos_of_taylor {b : JetEnclosure} {j : Jet2}
    (hj : j.SoundOn (Set.Icc (0:ℝ) 1)) (hb : b.ContainsOn j (Set.Icc (0:ℝ) 1))
    (haccept : 0 < b.value.lo+b.first.lo+b.second.lo/2) : 0 < j.value 1 :=
  haccept.trans_le (taylor_lower hj hb)

end JetEnclosure
end GeneralCK.Certificates.JetBounds



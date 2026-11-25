-- Prove2me | Definitions.Def_DetDLP_S8M_RenamedFits
-- name    : DetDLP_S8M_RenamedFits
-- status  : Definition
-- author  : @Bingsheng
-- created : 2026-11-25T05:59:37.991926+00:00
-- url     : https://prove2.me/theorems/049f05f1-e8d5-466e-80a4-c3e7615b38cc
-- title:
--   Fitting renamed arithmetic blocks
-- statement:
--   Natural-address fitting lemmas for rows, column sums, products, hash runs, and range checks after an arbitrary signal renaming.
-- source:
--   S. Liu, B. Zhang, and K. Ren, "A Deterministic Subexponential-time Algorithm for the Discrete Logarithm Problem", Zhejiang University Preprint, 23 November 2026, Section 2.4, Section 3 & Section 4, Lemma 2.4, Theorem 3.1 & Theorem 1.1 (pp. 9–19)

import Definitions.Def_DetDLP_S8M_RouteLift

set_option autoImplicit false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
namespace DetDLP.S8M.RenamedFits
open S8H0 RegisterMap NamedBlocks HashRows S8H.MakeCombinators S8H.PointAddresses

abbrev RF {k l : ℕ} (f : Fin k → Fin l) (c : NC) (u : B k) := Fits c (⟨u.core,f ∘ u.name⟩ : B l)
abbrev Source {s : Shape} {l : ℕ} (f : Fin (s.size+1) → Fin l) (r : Ref s) := (f r.source).val

variable {s : Shape} {l : ℕ} (f : Fin (s.size+1) → Fin l)

theorem row {n m : ℕ} {fn : ℕ → ℕ → ℕ} {r : Fin n → Fin m → Ref s} (t)
    (h : ∀ (i : Fin n) (j : Fin m), fn i j = Source f (r i j)) : RF f (rowN n m fn) (rows n m r t) :=
  ⟨⟨rfl,rfl,rfl,fun _ => rfl,fun _ => rfl⟩,fun i => h (finProdFinEquiv.symm i).1 (finProdFinEquiv.symm i).2⟩

theorem col {n : ℕ} {a b z c : ℕ → ℕ} {A B Z C : Fin n → Ref s} (v : Bool)
    (ha : ∀ i : Fin n, a i = Source f (A i)) (hb : ∀ i : Fin n, b i = Source f (B i))
    (hz : ∀ i : Fin n, z i = Source f (Z i)) (hc : ∀ i : Fin n, c i = Source f (C i)) :
    RF f (colN n a b z c) (NamedBlocks.add v A B Z C) := by
  refine ⟨add_spec _,fun i => ?_⟩; simp only [colN,(add_spec n).bit i]
  let k := (S8C.AddLayout.layout n).bit i
  change (if k.val%4=0 then _ else _) = Source f (colRef A B Z C k)
  unfold colRef; generalize hk : k.val%4 = x; have hj : k.val/4 < n := by have := k.isLt; change k.val < n*4 at this; omega
  rcases x with _|_|_|x <;> first | exact ha ⟨_,hj⟩ | exact hb ⟨_,hj⟩ | exact hz ⟨_,hj⟩ | exact hc ⟨_,hj⟩

abbrev WNames {s : Shape} {l : ℕ} (f : Fin (s.size+1) → Fin l) (a : ℕ → ℕ) (A : Word s) := ∀ j, a j = Source f (A j)

theorem prod {d o : ℕ} (hd : 1 ≤ d) {a b z : ℕ → ℕ} {A B Z : Word s}
    {R : Fin (Routes.G hd) → Ref s} (hw : ∀ i, o+i.val = Source f (R i))
    (ha : WNames f a A) (hb : WNames f b B) (hz : WNames f z Z) :
    RF f (prodN d (Routes.G hd) o a b z) (HashRows.product hd A B Z R) := by
  apply RouteLift.cat_map_spec
  · refine ⟨mul_spec hd,fun i => ?_⟩; have hh := (mul_spec hd).bit i
    simp only [S8H.PointAddresses.mul,wires_eq hd] at hh; exact (congrArg (o+·) hh).trans (hw _)
  · apply row; intro i j; fin_cases j
    · exact (congrArg (o+·) (ext_spec hd i)).trans (hw _)
    · change (if i.val<d then _ else _) = Source f (HashRows.busRef d A B Z i)
      unfold HashRows.busRef; split_ifs <;> first | apply ha | apply hb | apply hz

theorem hash {d o₁ o₂ pin : ℕ} {hd : 1 ≤ d} (p : ℕ) (w : Wires d hd s)
    {a x b z r q p₁ p₂ t cp c₁ c₂ c₃ : ℕ → ℕ}
    (hpin : pin = (f (Fin.last _)).val)
    (ha : WNames f a w.a) (hx : WNames f x w.x) (hb : WNames f b w.b) (hz : WNames f z w.z)
    (hr : WNames f r w.rem) (hq : WNames f q w.quot) (h₁ : WNames f p₁ w.prod1) (h₂ : WNames f p₂ w.prod2)
    (ht : WNames f t w.sum) (hp : WNames f cp w.cp)
    (ho : ∀ j, o₁+j.val = Source f (w.mul1 j)) (ho' : ∀ j, o₂+j.val = Source f (w.mul2 j))
    (hc : ∀ j : Fin (2*d), c₁ j = Source f (w.carry1 j)) (hc' : ∀ j : Fin (d+1), c₂ j = Source f (w.carry2 j))
    (hc'' : ∀ j : Fin (d+1), c₃ j = Source f (w.carry3 j)) :
    RF f (genHashN d (Routes.G hd) o₁ o₂ pin a x b z r q p₁ p₂ t cp c₁ c₂ c₃) (HashRows.block p w) :=
  RouteLift.cat_map_spec (RouteLift.cat_map_spec (prod f hd ho ha hx h₁) (prod f hd ho' hq (fun _ => hpin) h₂))
    (RouteLift.cat_map_spec (col f false (fun j => h₂ j) (fun j => hr j) (fun j => h₁ j) hc)
      (RouteLift.cat_map_spec (col f false (fun j => hr j) (fun j => hb j) (fun j => ht j) hc')
        (col f false (fun j => hz j) (fun j => hp j) (fun j => ht j) hc'')))

theorem checker {d pin o : ℕ} (p : ℕ) (path : GateRoutes.Path (triple d) s)
    (hpin : pin = (f (Fin.last _)).val)
    (hp : ∀ a, o + a.index.val = Source f (.reg (path a))) :
    RF f (EffCombinators.rangeN d pin o) (RangeRows.checker p path) := by
  apply col
  · intro i; unfold EffCombinators.wd RangeRows.pad; split_ifs with h
    · exact hp (.fst (.word ⟨i,h⟩))
    · exact hpin
  · intro i; unfold EffCombinators.wd RangeRows.pad; split_ifs with h
    · exact (Nat.add_assoc ..).trans (hp (.snd (.fst (.word ⟨i,h⟩))))
    · exact hpin
  · exact fun _ => hpin
  · intro i; have h := hp (.snd (.snd (.word i)))
    change o+(d+(d+i.val)) = _ at h
    exact (by omega : o+2*d+i.val = o+(d+(d+i.val))).trans h

end DetDLP.S8M.RenamedFits



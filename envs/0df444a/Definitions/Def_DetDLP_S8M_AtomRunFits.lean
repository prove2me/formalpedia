-- Prove2me | Definitions.Def_DetDLP_S8M_AtomRunFits
-- name    : DetDLP_S8M_AtomRunFits
-- status  : Definition
-- author  : @Bingsheng
-- created : 2026-11-25T06:23:49.151413+00:00
-- url     : https://prove2.me/theorems/81ad21c0-b031-42a5-90da-5500cc85e391
-- title:
--   Atom hash run address fit
-- statement:
--   Proves the pure numeric product, column and carry addresses in each of the seven register-bank hash runs under a routed embedding.
-- source:
--   S. Liu, B. Zhang, and K. Ren, "A Deterministic Subexponential-time Algorithm for the Discrete Logarithm Problem", Zhejiang University Preprint, 23 November 2026, Section 2.4, Section 3 & Section 4, Lemma 2.4, Theorem 3.1 & Theorem 1.1 (pp. 9–19)

import Definitions.Def_DetDLP_S8M_RenamedFits
import Definitions.Def_DetDLP_S8M_StepBaseDefs
set_option autoImplicit false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option linter.unusedSimpArgs false
namespace DetDLP.S8M.AtomRunFits
open S8H0 RegisterMap GateRoutes RangeRows NamedBlocks HashRows RenamedFits EffCombinators RouteLift
open S8H.MakeCombinators

abbrev stride (d e : ℕ) := 11*d+2*e+3
abbrev Z (o d e g : ℕ) := o+1+(3*d+1)+(3*d+1)+g*stride d e
abbrev U (o d e g : ℕ) := Z o d e 7+g*(5*d+3)

theorem hashRun {d l : ℕ} (hd : 1 ≤ d) (p : ℕ) (c : Coeff) (g : Fin 7)
    (o pin : ℕ) (f : Fin ((GateRoutes.S d (Routes.G hd)).size+1) → Fin l)
    (hp : pin = (f (Fin.last _)).val) (hr : ∀ a, Source f (.reg a) = o + a.index.val)
    (a x b : ℕ → ℕ) (ha : WNames f a (wires hd p c g).a) (hx : WNames f x (wires hd p c g).x)
    (hb : WNames f b (wires hd p c g).b) :
    RF f (StepBaseNat.hashN d (Routes.G hd) pin (Z o d (Routes.G hd) g) (U o d (Routes.G hd) g) a x b)
      (HashRows.block p (wires hd p c g)) := by
  have hmask (v : Bool) (a : Addr (S d (Routes.G hd))) : Source f (.masked v a) = o+a.index.val := hr a
  have hpin (v : Bool) : Source f (.pin v) = pin := hp.symm
  apply RenamedFits.hash f p _ hp ha hx hb
  all_goals intro j
  all_goals dsimp only [wires,wd,GateRoutes.word,padded,quot,rword]
  all_goals (try split_ifs) <;> first | exact hpin _ | exact (hpin _).symm | rw [hr] | rw [hmask]
  all_goals simp only [oa,ra,runPath,m1,m2,aux,cm,idxL,idxR,idxV,Shape.size,RegisterMap.mul,triple,run,auxShape,Z,U,stride]
  all_goals dsimp [Addr.index,Fin.castAdd,Fin.castLE,Fin.natAdd,EquivLike.coe,DFunLike.coe,EquivLike.toFunLike,Equiv.instEquivLike,Shape.size,RegisterMap.mul,triple,run,auxShape,finProdFinEquiv]
  all_goals ring

end DetDLP.S8M.AtomRunFits



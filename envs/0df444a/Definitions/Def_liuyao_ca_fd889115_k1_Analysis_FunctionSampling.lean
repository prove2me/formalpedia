-- Prove2me | Definitions.Def_liuyao_ca_fd889115_k1_Analysis_FunctionSampling
-- name    : liuyao_ca_fd889115_k1_Analysis_FunctionSampling
-- status  : Definition
-- author  : @liuyao
-- created : 2026-11-15T17:50:34.918791+00:00
-- url     : https://prove2.me/theorems/a2744f03-75a8-43b2-94d9-c93d6070570a
-- title:
--   Computable analysis · FunctionSampling · fd889115 k1
-- statement:
--   Private dependency for the Distribution Theory mission. Module ComputableAnalysis/FunctionSampling.lean from the frozen computable-analysis foundation with kernel-checked rational decision proofs.

import Definitions.Def_liuyao_ca_fd889115_k1_Analysis_Basic

set_option autoImplicit true

/-! Rational reparametrization and agreement on overlapping sample domains.
Different computations need not have identical domains. Composition of
agreement therefore retains an explicit intermediate-domain coverage proof. -/
namespace ComputableAnalysis

namespace PartialRealFunRaw

def pullback (f : PartialRealFunRaw) (coordinate : Rat → Rat) : PartialRealFunRaw where
  definedAt x := f.definedAt (coordinate x)
  compute x hx := f.compute (coordinate x) hx
  rate x hx := f.rate (coordinate x) hx

theorem pullback_valid (f : PartialRealFunRaw) (hf : f.Valid) (coordinate : Rat → Rat) :
    (f.pullback coordinate).Valid := fun x hx => hf (coordinate x) hx

def AgreeAlong (f g : PartialRealFunRaw) (left right : Rat → Rat) : Prop :=
  (f.pullback left).AgreeOnOverlap (g.pullback right)

/-- Chart coordinates may describe irrational physical points while the
samplers themselves still take only rational parameters. -/
def AgreeAtCoordinates (f g : PartialRealFunRaw) (left right : Rat → RealCompute) : Prop :=
  ∀ x y hx hy, (left x).Equiv (right y) → (f.evalRaw x hx).Equiv (g.evalRaw y hy)

theorem agreeAtCoordinates_symm {f g : PartialRealFunRaw} {left right : Rat → RealCompute}
    (h : f.AgreeAtCoordinates g left right) : g.AgreeAtCoordinates f right left :=
  fun y x hy hx he => RealCompute.equiv_symm (h x y hx hy (RealCompute.equiv_symm he))

theorem agreeAlong_symm {f g : PartialRealFunRaw} {left right : Rat → Rat}
    (h : f.AgreeAlong g left right) : g.AgreeAlong f right left :=
  agreeOnOverlap_symm h

theorem agreeOnOverlap_refl (f : PartialRealFunRaw) (hf : f.Valid) : f.AgreeOnOverlap f :=
  fun x hx _ => RealCompute.equiv_refl _ (hf x hx)

theorem agreeOnOverlap_trans_of_cover {f g h : PartialRealFunRaw}
    (hf : f.Valid) (hg : g.Valid) (hh : h.Valid)
    (hfg : f.AgreeOnOverlap g) (hgh : g.AgreeOnOverlap h)
    (cover : ∀ x, f.definedAt x → h.definedAt x → g.definedAt x) :
    f.AgreeOnOverlap h := by
  intro x hx hz
  let hy := cover x hx hz
  exact RealCompute.equiv_trans (x := f.evalRaw x hx) (y := g.evalRaw x hy)
    (z := h.evalRaw x hz) (hf x hx) (hg x hy) (hh x hz)
    (hfg x hx hy) (hgh x hy hz)

end PartialRealFunRaw

namespace FunctionRaw

def pullback (f : FunctionRaw) (coordinate : QComplex → QComplex) : FunctionRaw where
  domain z := f.domain (coordinate z)
  compute z hz := f.compute (coordinate z) hz
  rate z hz := f.rate (coordinate z) hz

theorem pullback_valid (f : FunctionRaw) (hf : f.Valid) (coordinate : QComplex → QComplex) :
    (f.pullback coordinate).Valid := fun z hz => hf (coordinate z) hz

def AgreeAlong (f g : FunctionRaw) (left right : QComplex → QComplex) : Prop :=
  (f.pullback left).AgreeOnCommonDomain (g.pullback right)

def AgreeAtCoordinates (f g : FunctionRaw) (left right : QComplex → ComplexCompute) : Prop :=
  ∀ z w hz hw, (left z).Equiv (right w) → (f.evalRaw z hz).Equiv (g.evalRaw w hw)

theorem agreeAtCoordinates_symm {f g : FunctionRaw}
    {left right : QComplex → ComplexCompute} (h : f.AgreeAtCoordinates g left right) :
    g.AgreeAtCoordinates f right left :=
  fun w z hw hz he => ComplexCompute.equiv_symm (h z w hz hw (ComplexCompute.equiv_symm he))

theorem agreeAlong_symm {f g : FunctionRaw} {left right : QComplex → QComplex}
    (h : f.AgreeAlong g left right) : g.AgreeAlong f right left :=
  agreeOnCommonDomain_symm h

theorem agreeOnCommonDomain_refl (f : FunctionRaw) (hf : f.Valid) :
    f.AgreeOnCommonDomain f := fun z hz _ => ComplexCompute.equiv_refl _ (hf z hz)

theorem agreeOnCommonDomain_trans_of_cover {f g h : FunctionRaw}
    (hf : f.Valid) (hg : g.Valid) (hh : h.Valid)
    (hfg : f.AgreeOnCommonDomain g) (hgh : g.AgreeOnCommonDomain h)
    (cover : ∀ z, f.domain z → h.domain z → g.domain z) :
    f.AgreeOnCommonDomain h := by
  intro z hz hw
  let hy := cover z hz hw
  exact ComplexCompute.equiv_trans (hf z hz) (hg z hy) (hh z hw)
    (hfg z hz hy) (hgh z hy hw)

theorem realPartOnRealAxis_valid (f : FunctionRaw) (hf : f.Valid) :
    f.realPartOnRealAxis.Valid := fun _x hx => ComplexCompute.realPart_valid (hf _ hx)

theorem realPartOnRealAxis_agrees {f g : FunctionRaw}
    (h : f.AgreeOnCommonDomain g) :
    f.realPartOnRealAxis.AgreeOnOverlap g.realPartOnRealAxis :=
  fun _x hx hg => ComplexCompute.realPart_equiv (h _ hx hg)

end FunctionRaw
end ComputableAnalysis



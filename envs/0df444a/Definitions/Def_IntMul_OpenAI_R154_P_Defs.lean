-- Prove2me | Definitions.Def_IntMul_OpenAI_R154_P_Defs
-- name    : IntMul_OpenAI_R154_P_Defs
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-10-20T03:01:03.660648+00:00
-- url     : https://prove2.me/theorems/e1a0419a-5226-4e30-aa16-c2fd27b40865
-- title:
--   κ-machine definitions at the frozen-154 constants
-- statement:
--   The 117 definitions of xuanji's $\kappa = 2^{-182}$ machine development (bundles `IntMul_Kappa_K_Defs9` to `IntMul_Kappa_K_Defs33`) that depend on the constants, re-declared under `IntMul.OpenAI.R154.P` with the constants of §8 replaced by those of the community patch `frozen-154`: $\varepsilon = c = 2^{-51}$, $\lambda' = 1 - 2^{-102}$ ($\tau = 1 - 2^{-50}$ and $\delta = 1/16$ unchanged). They are the parameter-dependent interfaces of the assembly (`P14Need`, `P14Uat`, `Par18Need`, `EwB18`, `P18IL`, `PhiNeed`, `LineNeed`, `ChirpNeedR`, the cost table `cLineU`, the setup program `setupA` computing $d = \lfloor b^{2^{-51}} \rfloor$ and $K = \lfloor d^{2^{-51}} \rfloor$ by exact root search, and the axis maps), copied verbatim apart from the constants; everything else is imported from `IntMul_Kappa_K_Defs33`. Also defines $r = 2^{\ell}$ (`rP`), $\gamma = 2 d \alpha^2$ (`γP`) for the `R154` parameter map, and `MachineGoal`, the statement of `IntMul.OpenAI.R154.machine`.
-- source:
--   OpenAI, Integer multiplication below n log n (preprint, 23 Sep 2026), https://github.com/openai/math/tree/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Integer-multiplication-below-n-log-n-September-23-2026, §8 and §9 with the frozen-154 constants of https://github.com/CrocSwap/integer-mult-bounds. Port of the definition bundles IntMul_Kappa_K_Defs9..33 by xuanji.

import Definitions.Def_IntMul_Kappa_K_Defs33
import Definitions.Def_IntMul_OpenAI_R154

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 1000000

namespace IntMul.OpenAI.R154

noncomputable section

/-- `r = 2^ℓ`. -/
def rP (n : ℕ) : ℕ := 2 ^ ℓP n
/-- `γ = 2 d α²`. -/
def γP (n : ℕ) : ℝ := 2 * (dP n : ℝ) * (αP n : ℝ) ^ 2

end

/-- The statement of `IntMul.OpenAI.R154.machine`: a correct multitape machine whose time on
large lengths is `O(V · Ncost · (log lg n + 1)^A + n)` at the `frozen-154` parameters. -/
def P.MachineGoal : Prop :=
  ∃ M : IntMul.MultitapeTM,
    (∀ n : ℕ, 1 ≤ n → ∃ T : ℝ, IntMul.MultipliesAt M n T) ∧
      ∃ C₀ : ℝ, 0 ≤ C₀ ∧ ∃ A n₁ : ℕ, ∀ n : ℕ, n₁ ≤ n → IntMul.MultipliesAt M n
        (C₀ * (IntMul.OpenAI.Glue.VP n *
          Ncost (6 * (IntMul.lg n : ℝ)) (dP n) (KP n) (ℓP n) (αP n) *
            (Real.log (IntMul.lg n) + 1) ^ A + n))

end IntMul.OpenAI.R154

-- from K_Defs21
section

set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
set_option linter.unusedSectionVars false

namespace IntMul.OpenAI.R154.P.NLogN.KFM
open _root_.NLogN hiding DE bitE fmB liftL parC
open _root_.NLogN.KFM hiding BaseOK BigCtx ChainSizes Close D18Regs DescRegs ErC EsN LRegs LineNeed NcN P18IL QRegs TrRegs bLn baseSt bigP bsN cLineU chirpGN descChirpN descLineN descPhiN dpN gapR kBigF kChirp kDig kFin kFinA kFt kFtF kGm kIn kInF kLine kMul kPhi kRd kShF kShl kSm lineG muN parQV prodN sB sBD sCmp setC setP setupA setupS setupSt srcN stD tB tBD tF tsN ubar wFR wU zsWf

open _root_.IntMul
open _root_.NLogN.KFN hiding cMv pcs
open _root_.NLogN.KFR
open _root_.AModel hiding hdPos






/-- The exponent gap `λ' − τ50 − 2^{-56}`. -/
noncomputable def gapR : ℝ := (1 - (2 : ℝ)⁻¹ ^ 102) - τ50 - (2 : ℝ)⁻¹ ^ 51

end IntMul.OpenAI.R154.P.NLogN.KFM

end

-- from K_Defs22
section

set_option linter.unusedSimpArgs false

namespace IntMul.OpenAI.R154.P.NLogN.KFM
open _root_.NLogN hiding DE bitE fmB liftL parC
open _root_.IntMul.OpenAI.R154.P.NLogN
open _root_.NLogN.KFM hiding BaseOK BigCtx ChainSizes Close D18Regs DescRegs ErC EsN LRegs LineNeed NcN P18IL QRegs TrRegs bLn baseSt bigP bsN cLineU chirpGN descChirpN descLineN descPhiN dpN gapR kBigF kChirp kDig kFin kFinA kFt kFtF kGm kIn kInF kLine kMul kPhi kRd kShF kShl kSm lineG muN parQV prodN sB sBD sCmp setC setP setupA setupS setupSt srcN stD tB tBD tF tsN ubar wFR wU zsWf
open _root_.IntMul.OpenAI.R154.P.NLogN.KFM

open _root_.IntMul
open _root_.IntMul.OpenAI.Glue hiding KP dP rP αP γP ℓP
open _root_.IntMul.OpenAI.R154


open _root_.NLogN.RS



/-- Part A: `d`, `K`, `α`. -/
def setupA : RS :=
  .seq (rootP 51 zB NLogN.KFM.zD) (.seq (rootP 51 NLogN.KFM.zD zK) (.seq (cntP NLogN.KFM.XE tstA zAl)
    (.asg zAl (.add (.reg zAl) (.lit 1)))))



/-- **The scalar setup program** (inputs `n` on `zN`, `b` on `zB`). -/
def setupS : RS := .seq setupA (.seq setupB setupC)

end IntMul.OpenAI.R154.P.NLogN.KFM

end

-- from K_Defs22
section

set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false

namespace IntMul.OpenAI.R154.P.NLogN.KFM
open _root_.NLogN hiding DE bitE fmB liftL parC
open _root_.IntMul.OpenAI.R154.P.NLogN
open _root_.NLogN.KFM hiding BaseOK BigCtx ChainSizes Close D18Regs DescRegs ErC EsN LRegs LineNeed NcN P18IL QRegs TrRegs bLn baseSt bigP bsN cLineU chirpGN descChirpN descLineN descPhiN dpN gapR kBigF kChirp kDig kFin kFinA kFt kFtF kGm kIn kInF kLine kMul kPhi kRd kShF kShl kSm lineG muN parQV prodN sB sBD sCmp setC setP setupA setupS setupSt srcN stD tB tBD tF tsN ubar wFR wU zsWf
open _root_.IntMul.OpenAI.R154.P.NLogN.KFM

open _root_.IntMul
open _root_.IntMul.OpenAI.Glue hiding KP dP rP αP γP ℓP
open _root_.IntMul.OpenAI.R154
open _root_.IntMul.OpenAI.RP
open _root_.NLogN.RS

/-- The state after `setupS`: `d, K, α, L, ℓ, r, d', Q, M_{r/2}, M_r` pushed on `zD … zMf`. -/
noncomputable def setupSt (n : ℕ) (s : IState HS) : IState HS :=
  let p := fun (t : IState HS) (i : Fin HS) (v : ℕ) => t.upd i (.int (v : ℤ) :: s.G i)
  p (p (p (p (p (p (p (p (p (p s NLogN.KFM.zD (dP n)) zK (KP n)) zAl (αP n)) zL (LP n)) zEl (ℓP n)) zR (IntMul.OpenAI.R154.rP n))
    zDp (mcnt (LP n) (dP n))) zQ (srcQ (dP n) (IntMul.OpenAI.R154.rP n))) zMh (srcM (dP n) (IntMul.OpenAI.R154.rP n) (IntMul.OpenAI.R154.rP n / 2)))
    zMf (srcM (dP n) (IntMul.OpenAI.R154.rP n) (IntMul.OpenAI.R154.rP n))

end IntMul.OpenAI.R154.P.NLogN.KFM

end

-- from K_Defs23
section

set_option linter.unusedSimpArgs false

namespace IntMul.OpenAI.R154.P.NLogN.KFM
open _root_.NLogN hiding DE bitE fmB liftL parC
open _root_.IntMul.OpenAI.R154.P.NLogN
open _root_.NLogN.KFM hiding BaseOK BigCtx ChainSizes Close D18Regs DescRegs ErC EsN LRegs LineNeed NcN P18IL QRegs TrRegs bLn baseSt bigP bsN cLineU chirpGN descChirpN descLineN descPhiN dpN gapR kBigF kChirp kDig kFin kFinA kFt kFtF kGm kIn kInF kLine kMul kPhi kRd kShF kShl kSm lineG muN parQV prodN sB sBD sCmp setC setP setupA setupS setupSt srcN stD tB tBD tF tsN ubar wFR wU zsWf
open _root_.IntMul.OpenAI.R154.P.NLogN.KFM

open _root_.IntMul
open _root_.IntMul.OpenAI.Glue hiding KP dP rP αP γP ℓP
open _root_.IntMul.OpenAI.R154
open _root_.IntMul.OpenAI.RP

/-- `d' = dℓ − L`. -/
noncomputable def dpN (n : ℕ) : ℕ := mcnt (IntMul.OpenAI.Glue.LP n) (IntMul.OpenAI.R154.dP n)

/-- The source `s_i`. -/
noncomputable def srcN (n i : ℕ) : ℕ := srcS (IntMul.OpenAI.R154.dP n) (dpN n) (IntMul.OpenAI.R154.rP n) i

/-- `P_i = ∏_{j<i} s_j`. -/
noncomputable def prodN (n i : ℕ) : ℕ := ∏ j ∈ Finset.range i, srcN n j

/-- `μ_i = P_i^{-1} mod s_i`. -/
noncomputable def muN (n i : ℕ) : ℕ := muInv (prodN n i) (srcN n i)


end IntMul.OpenAI.R154.P.NLogN.KFM

end

-- from K_Defs23
section

namespace IntMul.OpenAI.R154.P.NLogN.KFM
open _root_.NLogN hiding DE bitE fmB liftL parC
open _root_.IntMul.OpenAI.R154.P.NLogN
open _root_.NLogN.KFM hiding BaseOK BigCtx ChainSizes Close D18Regs DescRegs ErC EsN LRegs LineNeed NcN P18IL QRegs TrRegs bLn baseSt bigP bsN cLineU chirpGN descChirpN descLineN descPhiN dpN gapR kBigF kChirp kDig kFin kFinA kFt kFtF kGm kIn kInF kLine kMul kPhi kRd kShF kShl kSm lineG muN parQV prodN sB sBD sCmp setC setP setupA setupS setupSt srcN stD tB tBD tF tsN ubar wFR wU zsWf
open _root_.IntMul.OpenAI.R154.P.NLogN.KFM

open _root_.IntMul
open _root_.NLogN.KIL hiding Cfg FR St aE aK cMv cStep cstep gS negP outR pT padL rJ1 rS rT sI stD tB zB zR
open _root_.NLogN.KFB hiding permL permP rB2 rG rN
open _root_.NLogN.KFH
open _root_.IntMul.OpenAI.Glue hiding KP dP rP αP γP ℓP
open _root_.IntMul.OpenAI.R154
open _root_.IntMul.OpenAI.RCost hiding Ncost c es lam' δ ε κ τ
open _root_.IntMul.OpenAI.R154

noncomputable section


/-- **Proposition 18 in IL** (hypothesis of the assembly; to be proved in item 13). -/
def P18IL : Prop :=
  ∃ (E : ℕ) (ext : Fin E → IStmt HS (7 + E)) (entry : Fin (7 + E)) (dS : Fin HS)
    (C₀ : ℝ) (A n₁ : ℕ), dS ≠ 0 ∧ 0 ≤ C₀ ∧
  ∀ (Isym : List Sym) (n : ℕ), IntMul.OpenAI.Glue.n0 ≤ n → n₁ ≤ n →
  ∀ (ts : List ℕ), ts.length + 1 = IntMul.OpenAI.R154.dP n → (∀ t ∈ ts, t = IntMul.OpenAI.R154.rP n ∨ 2 * t = IntMul.OpenAI.R154.rP n) →
  ∀ (s : IState HS) (f : Fin HS → List ℤ) (zf zg : List GI) (l : List ℤ)
    (xf xg : List (Fin (IntMul.OpenAI.R154.rP n) → ℂ)),
    (∀ j, j ≠ 0 → j ≠ dS → f j = []) →
    f dS = desc18 (pP n) (ℓP n) (KP n) ts →
    f 0 = gflat zf ++ gflat zg ++ l →
    RecRep (IntMul.OpenAI.R154.rP n) (pP n) zf xf → RecRep (IntMul.OpenAI.R154.rP n) (pP n) zg xg →
    xf.length = ts.prod → xg.length = ts.prod →
    NLogN.KFB.GB (pP n + 2) zf → NLogN.KFB.GB (pP n + 2) zg →
    (∀ x ∈ xf, ‖x‖ ≤ 1) → (∀ x ∈ xg, ‖x‖ ≤ 1) →
    ∃ (zh : List GI) (xh : List (Fin (IntMul.OpenAI.R154.rP n) → ℂ)) (c : ℕ),
      IRuns Isym (kTable ext) (.call entry) (NLogN.KIL.encK s f)
        (NLogN.KIL.encK s (Function.update f 0 (gflat zh ++ l))) c ∧
      RecRep (IntMul.OpenAI.R154.rP n) (pP n) zh xh ∧ xh.length = ts.prod ∧ NLogN.KFB.GB (pP n + 2) zh ∧
      (∀ j < ts.prod, ∀ k : Fin (IntMul.OpenAI.R154.rP n),
        ‖xh.getD j 0 k - (mrL (IntMul.OpenAI.R154.rP n) ts xf xg).getD j 0 k‖ ≤
          2 * ts.prod * (3 * ℓP n + 1) * (2 : ℝ)⁻¹ ^ pP n) ∧
      (c : ℝ) ≤ C₀ * ((ts.prod * IntMul.OpenAI.R154.rP n * (pP n + 3) : ℕ) : ℝ) *
        Ncost (6 * (lg n : ℝ)) (IntMul.OpenAI.R154.dP n) (KP n) (ℓP n) (αP n) *
        (Real.log (6 * (lg n : ℝ)) + 1) ^ A

end

end IntMul.OpenAI.R154.P.NLogN.KFM

end

-- from K_Defs23
section

set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false

namespace IntMul.OpenAI.R154.P.NLogN.KFM
open _root_.NLogN hiding DE bitE fmB liftL parC
open _root_.IntMul.OpenAI.R154.P.NLogN
open _root_.NLogN.KFM hiding BaseOK BigCtx ChainSizes Close D18Regs DescRegs ErC EsN LRegs LineNeed NcN P18IL QRegs TrRegs bLn baseSt bigP bsN cLineU chirpGN descChirpN descLineN descPhiN dpN gapR kBigF kChirp kDig kFin kFinA kFt kFtF kGm kIn kInF kLine kMul kPhi kRd kShF kShl kSm lineG muN parQV prodN sB sBD sCmp setC setP setupA setupS setupSt srcN stD tB tBD tF tsN ubar wFR wU zsWf
open _root_.IntMul.OpenAI.R154.P.NLogN.KFM

open _root_.IntMul
open _root_.IntMul.OpenAI.Glue hiding KP dP rP αP γP ℓP
open _root_.IntMul.OpenAI.R154
open _root_.IntMul.OpenAI.RP
open _root_.NLogN.RS





/-- The bits of `n`: `t_j = r` exactly when `j ≥ d'`. -/
noncomputable def bLn (n : ℕ) (j : ℕ) : Bool := decide (dpN n ≤ j)

/-- The registers the descriptor code reads, for `n`. -/
structure DescRegs (t : IState HS) (n w : ℕ) (rw : Fin HS) : Prop where
  src : SrcRegs t (dpN n) (srcQ (IntMul.OpenAI.R154.dP n) (IntMul.OpenAI.R154.rP n)) (srcM (IntMul.OpenAI.R154.dP n) (IntMul.OpenAI.R154.rP n) (IntMul.OpenAI.R154.rP n / 2))
    (srcM (IntMul.OpenAI.R154.dP n) (IntMul.OpenAI.R154.rP n) (IntMul.OpenAI.R154.rP n))
  hD : ∃ L, t.G zD = .int (IntMul.OpenAI.R154.dP n : ℤ) :: L
  hEl : ∃ L, t.G zEl = .int (ℓP n : ℤ) :: L
  hW : ∃ L, t.G rw = .int (w : ℤ) :: L

end IntMul.OpenAI.R154.P.NLogN.KFM

end

-- from K_Defs23
section

set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false

namespace IntMul.OpenAI.R154.P.NLogN.KFM
open _root_.NLogN hiding DE bitE fmB liftL parC
open _root_.IntMul.OpenAI.R154.P.NLogN
open _root_.NLogN.KFM hiding BaseOK BigCtx ChainSizes Close D18Regs DescRegs ErC EsN LRegs LineNeed NcN P18IL QRegs TrRegs bLn baseSt bigP bsN cLineU chirpGN descChirpN descLineN descPhiN dpN gapR kBigF kChirp kDig kFin kFinA kFt kFtF kGm kIn kInF kLine kMul kPhi kRd kShF kShl kSm lineG muN parQV prodN sB sBD sCmp setC setP setupA setupS setupSt srcN stD tB tBD tF tsN ubar wFR wU zsWf
open _root_.IntMul.OpenAI.R154.P.NLogN.KFM

open _root_.IntMul
open _root_.IntMul.OpenAI.Glue hiding KP dP rP αP γP ℓP
open _root_.IntMul.OpenAI.R154
open _root_.IntMul.OpenAI.RP
open _root_.NLogN.RS






/-- The axis lengths for `n`. -/
noncomputable def tsN (n : ℕ) : List ℕ :=
  (List.range (IntMul.OpenAI.R154.dP n - 1)).map fun j => if dpN n ≤ j then IntMul.OpenAI.R154.rP n else IntMul.OpenAI.R154.rP n / 2


/-- The registers `desc18P` reads. -/
structure D18Regs (t : IState HS) (n : ℕ) : Prop where
  hD : ∃ L, t.G zD = .int (IntMul.OpenAI.R154.dP n : ℤ) :: L
  hDp : ∃ L, t.G zDp = .int (dpN n : ℤ) :: L
  hR : ∃ L, t.G zR = .int (IntMul.OpenAI.R154.rP n : ℤ) :: L
  hK : ∃ L, t.G zK = .int (KP n : ℤ) :: L
  hEl : ∃ L, t.G zEl = .int (ℓP n : ℤ) :: L
  hB : ∃ L, t.G NLogN.KFM.zB = .int (bP n : ℤ) :: L


end IntMul.OpenAI.R154.P.NLogN.KFM

end

-- from K_Defs23
section

set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false

namespace IntMul.OpenAI.R154.P.NLogN.KFM
open _root_.NLogN hiding DE bitE fmB liftL parC
open _root_.IntMul.OpenAI.R154.P.NLogN
open _root_.NLogN.KFM hiding BaseOK BigCtx ChainSizes Close D18Regs DescRegs ErC EsN LRegs LineNeed NcN P18IL QRegs TrRegs bLn baseSt bigP bsN cLineU chirpGN descChirpN descLineN descPhiN dpN gapR kBigF kChirp kDig kFin kFinA kFt kFtF kGm kIn kInF kLine kMul kPhi kRd kShF kShl kSm lineG muN parQV prodN sB sBD sCmp setC setP setupA setupS setupSt srcN stD tB tBD tF tsN ubar wFR wU zsWf
open _root_.IntMul.OpenAI.R154.P.NLogN.KFM

open _root_.IntMul
open _root_.IntMul.OpenAI.Glue hiding KP dP rP αP γP ℓP
open _root_.IntMul.OpenAI.R154
open _root_.IntMul.OpenAI.RP
open _root_.NLogN.RS




/-- The rotated bits for `n` after `m` rotations. -/
noncomputable def bsN (n m : ℕ) : List Bool :=
  (List.range (IntMul.OpenAI.R154.dP n)).map fun j => decide (dpN n ≤ (j + m) % IntMul.OpenAI.R154.dP n)


/-- The registers `descTrP` reads. -/
structure TrRegs (t : IState HS) (n w m : ℕ) (rw rm : Fin HS) : Prop where
  hD : ∃ L, t.G zD = .int (IntMul.OpenAI.R154.dP n : ℤ) :: L
  hDp : ∃ L, t.G zDp = .int (dpN n : ℤ) :: L
  hEl : ∃ L, t.G zEl = .int (ℓP n : ℤ) :: L
  hW : ∃ L, t.G rw = .int (w : ℤ) :: L
  hM : ∃ L, t.G rm = .int (m : ℤ) :: L

end IntMul.OpenAI.R154.P.NLogN.KFM

end

-- from K_Defs23
section

namespace IntMul.OpenAI.R154.P.NLogN.KFM
open _root_.NLogN hiding DE bitE fmB liftL parC
open _root_.IntMul.OpenAI.R154.P.NLogN
open _root_.NLogN.KFM hiding BaseOK BigCtx ChainSizes Close D18Regs DescRegs ErC EsN LRegs LineNeed NcN P18IL QRegs TrRegs bLn baseSt bigP bsN cLineU chirpGN descChirpN descLineN descPhiN dpN gapR kBigF kChirp kDig kFin kFinA kFt kFtF kGm kIn kInF kLine kMul kPhi kRd kShF kShl kSm lineG muN parQV prodN sB sBD sCmp setC setP setupA setupS setupSt srcN stD tB tBD tF tsN ubar wFR wU zsWf
open _root_.IntMul.OpenAI.R154.P.NLogN.KFM

open _root_.IntMul
open _root_.NLogN.KIL hiding Cfg FR St aE aK cMv cStep cstep gS negP outR pT padL rJ1 rS rT sI stD tB zB zR
open _root_.NLogN.KFB hiding permL permP rB2 rG rN
open _root_.IntMul.HvdH
open _root_.IntMul.OpenAI.RT
open _root_.IntMul.OpenAI.Glue hiding KP dP rP αP γP ℓP
open _root_.IntMul.OpenAI.R154
open _root_.IntMul.OpenAI.RCost hiding Ncost c es lam' δ ε κ τ
open _root_.IntMul.OpenAI.R154

noncomputable section

/-- The source lengths as a box. -/
def sB (n : ℕ) : Fin (IntMul.OpenAI.R154.dP n) → ℕ := fun i => srcN n i

/-- The padded lengths as a box (`r` from `d'` on, else `r/2`). -/
def tB (n : ℕ) : Fin (IntMul.OpenAI.R154.dP n) → ℕ := fun i => if dpN n ≤ i.val then IntMul.OpenAI.R154.rP n else IntMul.OpenAI.R154.rP n / 2







/-- The line-map descriptor for `n`. -/
def descLineN (n : ℕ) : List ℤ :=
  descLine (pP n) (αP n) (ℓP n - 1) (IntMul.OpenAI.R154.dP n) (bLn n) (srcN n)

/-- The cost allowed for one line-map phase (as `P18IL`). -/
def cLineU (n A : ℕ) : ℝ :=
  VP n * Ncost (6 * (IntMul.lg n : ℝ)) (IntMul.OpenAI.R154.dP n) (KP n) (ℓP n) (αP n) *
    (Real.log (6 * (IntMul.lg n : ℝ)) + 1) ^ A

/-- **The line maps in IL, uniform** (hypothesis of the assembly). -/
def LineNeed : Prop :=
  ∃ (E : ℕ) (ext : Fin E → IStmt HS (7 + E)) (eA eB : Fin (7 + E)) (dS : Fin HS) (C₀ : ℝ)
    (A n₁ : ℕ), dS ≠ 0 ∧ 0 ≤ C₀ ∧
  ∀ (Isym : List Sym) (n : ℕ), IntMul.OpenAI.Glue.n0 ≤ n → n₁ ≤ n →
  ∀ [∀ i, NeZero (IntMul.OpenAI.R154.P.NLogN.KFM.sB n i)] [∀ i, NeZero (IntMul.OpenAI.R154.P.NLogN.KFM.tB n i)],
  ∀ (s : IState HS) (f : Fin HS → List ℤ) (l : List ℤ),
    (∀ j, j ≠ 0 → j ≠ dS → f j = []) →
    f dS = descLineN n →
    (∀ (zs : List GI) (u : ((i : Fin (IntMul.OpenAI.R154.dP n)) → ZMod (IntMul.OpenAI.R154.P.NLogN.KFM.sB n i)) → ℂ),
      f 0 = gflat zs ++ l → RepPad (pP n) (IntMul.OpenAI.R154.P.NLogN.KFM.sB n) (IntMul.OpenAI.R154.P.NLogN.KFM.tB n) zs u → ‖u‖ ≤ 1 / 2 →
      ∃ (zs' : List GI) (w : ((i : Fin (IntMul.OpenAI.R154.dP n)) → ZMod (IntMul.OpenAI.R154.P.NLogN.KFM.tB n i)) → ℂ) (c : ℕ),
        IRuns Isym (kTable ext) (.call eA) (NLogN.KIL.encK s f)
          (NLogN.KIL.encK s (Function.update f 0 (gflat zs' ++ l))) c ∧
        RepFull (pP n) (IntMul.OpenAI.R154.P.NLogN.KFM.tB n) zs' w ∧ NLogN.KFB.GB (pP n + 2) zs' ∧
        (∀ M : AxisMaps (d := IntMul.OpenAI.R154.dP n) (pP n) (αP n) (IntMul.OpenAI.R154.P.NLogN.KFM.sB n) (IntMul.OpenAI.R154.P.NLogN.KFM.tB n),
          ‖w - tensCLM (kerA M.A) u‖ ≤ epsA (pP n) (αP n) (IntMul.OpenAI.R154.dP n) * hp (pP n)) ∧
        (c : ℝ) ≤ C₀ * cLineU n A) ∧
    (∀ (ys : List GI) (y : ((i : Fin (IntMul.OpenAI.R154.dP n)) → ZMod (IntMul.OpenAI.R154.P.NLogN.KFM.tB n i)) → ℂ),
      f 0 = gflat ys ++ l → RepFull (pP n) (IntMul.OpenAI.R154.P.NLogN.KFM.tB n) ys y → ‖y‖ ≤ 1 →
      ∃ (ys' : List GI) (v : ((i : Fin (IntMul.OpenAI.R154.dP n)) → ZMod (IntMul.OpenAI.R154.P.NLogN.KFM.sB n i)) → ℂ) (c : ℕ),
        IRuns Isym (kTable ext) (.call eB) (NLogN.KIL.encK s f)
          (NLogN.KIL.encK s (Function.update f 0 (gflat ys' ++ l))) c ∧
        RepPad (pP n) (IntMul.OpenAI.R154.P.NLogN.KFM.sB n) (IntMul.OpenAI.R154.P.NLogN.KFM.tB n) ys' v ∧ NLogN.KFB.GB (pP n + 2) ys' ∧
        (∀ M : AxisMaps (d := IntMul.OpenAI.R154.dP n) (pP n) (αP n) (IntMul.OpenAI.R154.P.NLogN.KFM.sB n) (IntMul.OpenAI.R154.P.NLogN.KFM.tB n),
          ‖v - tensCLM (kerB M.B) y‖ ≤ epsB (pP n) (αP n) (IntMul.OpenAI.R154.P.NLogN.KFM.sB n) (IntMul.OpenAI.R154.P.NLogN.KFM.tB n) * hp (pP n)) ∧
        (c : ℝ) ≤ C₀ * cLineU n A)

end

end IntMul.OpenAI.R154.P.NLogN.KFM

end

-- from K_Defs24
section

namespace IntMul.OpenAI.R154.P.NLogN.KFM
open _root_.NLogN hiding DE bitE fmB liftL parC
open _root_.IntMul.OpenAI.R154.P.NLogN
open _root_.NLogN.KFM hiding BaseOK BigCtx ChainSizes Close D18Regs DescRegs ErC EsN LRegs LineNeed NcN P18IL QRegs TrRegs bLn baseSt bigP bsN cLineU chirpGN descChirpN descLineN descPhiN dpN gapR kBigF kChirp kDig kFin kFinA kFt kFtF kGm kIn kInF kLine kMul kPhi kRd kShF kShl kSm lineG muN parQV prodN sB sBD sCmp setC setP setupA setupS setupSt srcN stD tB tBD tF tsN ubar wFR wU zsWf
open _root_.IntMul.OpenAI.R154.P.NLogN.KFM

open _root_.IntMul
open _root_.NLogN.KIL hiding Cfg FR St aE aK cMv cStep cstep gS negP outR pT padL rJ1 rS rT sI stD tB zB zR
open _root_.NLogN.KFB hiding permL permP rB2 rG rN
open _root_.IntMul.HvdH
open _root_.IntMul.OpenAI.RT
open _root_.IntMul.OpenAI.RC
open _root_.IntMul.OpenAI.Glue hiding KP dP rP αP γP ℓP
open _root_.IntMul.OpenAI.R154
open _root_.IntMul.OpenAI.RCost hiding Ncost c es lam' δ ε κ τ
open _root_.IntMul.OpenAI.R154

noncomputable section

/-- The source lengths as a `(D+1)`-box. -/
def sBD (n D : ℕ) : Fin (D + 1) → ℕ := fun i => srcN n i.val

/-- The padded lengths as a `(D+1)`-box. -/
def tBD (n D : ℕ) : Fin (D + 1) → ℕ := fun i => if dpN n ≤ i.val then IntMul.OpenAI.R154.rP n else IntMul.OpenAI.R154.rP n / 2

/-- The Prop 18 error constant (records along the last axis). -/
def ErC (n D : ℕ) : ℝ := 2 * ((∏ i : Fin D, tBD n D i.castSucc : ℕ) : ℝ) * (3 * ℓP n + 1)

/-- The chirp descriptor: `K :: descLineN n`. -/
def descChirpN (n : ℕ) : List ℤ := (KP n : ℤ) :: descLineN n

end

end IntMul.OpenAI.R154.P.NLogN.KFM

end

-- from K_Defs24
section

set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false

namespace IntMul.OpenAI.R154.P.NLogN.KFM
open _root_.NLogN hiding DE bitE fmB liftL parC
open _root_.IntMul.OpenAI.R154.P.NLogN
open _root_.NLogN.KFM hiding BaseOK BigCtx ChainSizes Close D18Regs DescRegs ErC EsN LRegs LineNeed NcN P18IL QRegs TrRegs bLn baseSt bigP bsN cLineU chirpGN descChirpN descLineN descPhiN dpN gapR kBigF kChirp kDig kFin kFinA kFt kFtF kGm kIn kInF kLine kMul kPhi kRd kShF kShl kSm lineG muN parQV prodN sB sBD sCmp setC setP setupA setupS setupSt srcN stD tB tBD tF tsN ubar wFR wU zsWf
open _root_.IntMul.OpenAI.R154.P.NLogN.KFM

open _root_.IntMul
open _root_.IntMul.OpenAI.Glue hiding KP dP rP αP γP ℓP
open _root_.IntMul.OpenAI.R154
open _root_.IntMul.OpenAI.RP
open _root_.NLogN.RS




/-- The registers the descriptor code reads. -/
structure LRegs (t : IState HS) (n : ℕ) : Prop where
  src : SrcRegs t (dpN n) (srcQ (IntMul.OpenAI.R154.dP n) (IntMul.OpenAI.R154.rP n)) (srcM (IntMul.OpenAI.R154.dP n) (IntMul.OpenAI.R154.rP n) (IntMul.OpenAI.R154.rP n / 2))
    (srcM (IntMul.OpenAI.R154.dP n) (IntMul.OpenAI.R154.rP n) (IntMul.OpenAI.R154.rP n))
  hD : ∃ L, t.G zD = .int (IntMul.OpenAI.R154.dP n : ℤ) :: L
  hEl : ∃ L, t.G zEl = .int (ℓP n : ℤ) :: L
  hAl : ∃ L, t.G zAl = .int (αP n : ℤ) :: L
  hB : ∃ L, t.G NLogN.KFM.zB = .int (bP n : ℤ) :: L
  hK : ∃ L, t.G zK = .int (KP n : ℤ) :: L

end IntMul.OpenAI.R154.P.NLogN.KFM

end

-- from K_Defs24
section

namespace IntMul.OpenAI.R154.P.NLogN.KFZ
open _root_.NLogN hiding St T1 T2 T3 T4 T5 T6 T7 tE
open _root_.IntMul.OpenAI.R154.P.NLogN
open _root_.NLogN.KFZ hiding BN ChirpNeedR bitN bsN hN length_bsN length_ssN ssN σN

open _root_.IntMul
open _root_.NLogN.KIL hiding Cfg FR St aE cBody negP outR padL pushF pushes
open _root_.NLogN.KFB hiding permL permP qA qT
open _root_.IntMul.HvdH
open _root_.IntMul.OpenAI.RT
open _root_.IntMul.OpenAI.RC
open _root_.IntMul.OpenAI.Glue hiding KP dP rP αP γP ℓP
open _root_.IntMul.OpenAI.R154
open _root_.IntMul.OpenAI.RCost hiding Ncost c es lam' δ ε κ τ
open _root_.IntMul.OpenAI.R154
open _root_.NLogN.KFM hiding BaseOK BigCtx ChainSizes Close D18Regs DE DescRegs ErC EsN LRegs LineNeed NcN P18IL QRegs TrRegs bLn baseSt bigP bitE bsN cLineU chirpGN descChirpN descLineN descPhiN dpN eB eN fmB gapR gconj kBigF kChirp kDig kFin kFinA kFt kFtF kGm kIn kInF kLine kMul kPhi kRd kShF kShl kSm liftL lineG muN parC parQV prodN sB sBD sCmp setC setP setupA setupS setupSt srcN stD sumB tB tBD tF tsN ubar wFR wU zsWf
open _root_.IntMul.OpenAI.R154.P.NLogN.KFM

noncomputable section

/-- **`ChirpNeed` with `M̃r` chosen per call** (after the input and the state). -/
def ChirpNeedR : Prop :=
  ∃ (E : ℕ) (ext : Fin E → IStmt HS (7 + E)) (eC : Fin (7 + E)) (dS : Fin HS) (C₀ : ℝ)
    (A n₁ : ℕ), dS ≠ 0 ∧ 0 ≤ C₀ ∧
  ∀ (n : ℕ), IntMul.OpenAI.Glue.n0 ≤ n → n₁ ≤ n → ∀ (D : ℕ), IntMul.OpenAI.R154.dP n = D + 1 →
  ∀ [∀ i, NeZero (tBD n D i)],
  ∃ (θt θit at' bt : ((i : Fin (D + 1)) → ZMod (tBD n D i)) → ℂ) (ζ : ℂ),
    ζ ^ tBD n D (Fin.last D) = -1 ∧
    Phases (pP n) (twX (tBD n D) ζ) θt ∧
    Phases (pP n) (fun j => (twX (tBD n D) ζ j)⁻¹) θit ∧
    Phases (pP n) (fun j => (starRingEnd ℂ) (chirp (sBD n D) (tBD n D) j)) at' ∧
    Phases (pP n) (chirp (sBD n D) (tBD n D)) bt ∧
    Grid (pP n) bt ∧ Grid (pP n) θit ∧
  ∀ (Isym : List Sym) (s : IState HS) (f : Fin HS → List ℤ) (l : List ℤ),
    (∀ j, j ≠ 0 → j ≠ dS → f j = []) →
    f dS = descChirpN n →
    ∀ (xs : List GI) (x : ((i : Fin (D + 1)) → ZMod (tBD n D i)) → ℂ),
      f 0 = gflat xs ++ l → RepFull (pP n) (tBD n D) xs x → ‖x‖ ≤ 6 / 10 →
      ∃ (Mrt : (((i : Fin (D + 1)) → ZMod (tBD n D i)) → ℂ) →
          (((i : Fin (D + 1)) → ZMod (tBD n D i)) → ℂ) →
          (((i : Fin (D + 1)) → ZMod (tBD n D i)) → ℂ)),
        (∀ f g, Grid (pP n) f → Grid (pP n) g → ‖f‖ ≤ 1 → ‖g‖ ≤ 1 →
          ‖Mrt f g - mrX (tBD n D) f g‖ ≤ ErC n D * hp (pP n)) ∧
      ∃ (ys : List GI) (c : ℕ),
        IRuns Isym (kTable ext) (.call eC) (NLogN.KIL.encK s f)
          (NLogN.KIL.encK s (Function.update f 0 (gflat ys ++ l))) c ∧
        RepFull (pP n) (tBD n D) ys (chirpT (pP n) (mcT (pP n) Mrt θt θit) bt at' x) ∧
        NLogN.KFB.GB (pP n + 2) ys ∧
        (c : ℝ) ≤ C₀ * cLineU n A

variable {D : ℕ}

end

end IntMul.OpenAI.R154.P.NLogN.KFZ

end

-- from K_Defs24
section

set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false

namespace IntMul.OpenAI.R154.P.NLogN.KFM
open _root_.NLogN hiding DE bitE fmB liftL parC
open _root_.IntMul.OpenAI.R154.P.NLogN
open _root_.NLogN.KFM hiding BaseOK BigCtx ChainSizes Close D18Regs DescRegs ErC EsN LRegs LineNeed NcN P18IL QRegs TrRegs bLn baseSt bigP bsN cLineU chirpGN descChirpN descLineN descPhiN dpN gapR kBigF kChirp kDig kFin kFinA kFt kFtF kGm kIn kInF kLine kMul kPhi kRd kShF kShl kSm lineG muN parQV prodN sB sBD sCmp setC setP setupA setupS setupSt srcN stD tB tBD tF tsN ubar wFR wU zsWf
open _root_.IntMul.OpenAI.R154.P.NLogN.KFM

open _root_.IntMul
open _root_.IntMul.OpenAI.Glue hiding KP dP rP αP γP ℓP
open _root_.IntMul.OpenAI.R154
open _root_.NLogN.RS






/-- The values of `parQ`, in push order. -/
noncomputable def parQV (n S : ℕ) : List (Fin HS × ℤ) :=
  [(NLogN.KFM.rT, 2 ^ IntMul.OpenAI.Glue.LP n), (rT2, 2 ^ (IntMul.OpenAI.Glue.LP n + 1)), (NLogN.KFM.rM, ((n + bP n - 1) / bP n : ℕ)),
   (rP2, 2 ^ pP n), (rG, 2 ^ (2 * IntMul.OpenAI.R154.dP n * αP n ^ 2)), (rE2, 2 ^ (pP n - bP n - 2)),
   (rB2, 2 ^ bP n), (rZ, 2 * ((S : ℤ) - ((n + bP n - 1) / bP n : ℕ))), (NLogN.KFM.rH, 2 ^ (pP n - 1)),
   (rF, 2 ^ (2 * bP n + 4)), (rPw, ((pP n + 2 : ℕ) : ℤ)), (rOne, 1)]


/-- The facts `parQ` reads. -/
structure QRegs (t : IState HS) (n S : ℕ) : Prop where
  hL : Hold t NLogN.KFM.zL (IntMul.OpenAI.Glue.LP n)
  hN : Hold t NLogN.KFM.zN n
  hB : Hold t NLogN.KFM.zB (bP n)
  hD : Hold t zD (IntMul.OpenAI.R154.dP n)
  hA : Hold t zAl (αP n)
  hS : Hold t NLogN.KFM.rS S

end IntMul.OpenAI.R154.P.NLogN.KFM

end

-- from K_Defs24
section

set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false

namespace IntMul.OpenAI.R154.P.NLogN.KFM
open _root_.NLogN hiding DE bitE fmB liftL parC
open _root_.IntMul.OpenAI.R154.P.NLogN
open _root_.NLogN.KFM hiding BaseOK BigCtx ChainSizes Close D18Regs DescRegs ErC EsN LRegs LineNeed NcN P18IL QRegs TrRegs bLn baseSt bigP bsN cLineU chirpGN descChirpN descLineN descPhiN dpN gapR kBigF kChirp kDig kFin kFinA kFt kFtF kGm kIn kInF kLine kMul kPhi kRd kShF kShl kSm lineG muN parQV prodN sB sBD sCmp setC setP setupA setupS setupSt srcN stD tB tBD tF tsN ubar wFR wU zsWf
open _root_.IntMul.OpenAI.R154.P.NLogN.KFM

open _root_.IntMul
open _root_.IntMul.OpenAI.Glue hiding KP dP rP αP γP ℓP
open _root_.IntMul.OpenAI.R154
open _root_.NLogN.RS
open _root_.NLogN.KFT hiding carW tE zB

variable {P : ℕ} {I : List Sym} {iprog : Fin P → IStmt HS P}







/-- The setup program. -/
def setP : IStmt HS P :=
  .seq startP (.seq setupS.code (.seq parS.code (.seq parQ.code oP)))

/-- `S` as computed (`= ∏ s_i` for large `n`). -/
noncomputable def sCmp (n : ℕ) : ℕ := (∏ j ∈ Finset.range (IntMul.OpenAI.R154.dP n), srcN n j) % 2 ^ bP n


/-- The state after step 3. -/
noncomputable def stD (x y : List Bool) : IState HS :=
  let n := x.length
  let sB := setupSt n (stA x y)
  NLogN.KFM.pushV (sB.upd NLogN.KFM.rS (.int (sCmp n : ℤ) :: sB.G NLogN.KFM.rS)) (parQV n (sCmp n))

/-- **The base state** of the main computation. -/
noncomputable def baseSt (x y : List Bool) : IState HS :=
  (IntMul.OpenAI.R154.P.NLogN.KFM.stD x y).upd rO (.int ((2 : ℤ) ^ (2 * x.length)) :: (IntMul.OpenAI.R154.P.NLogN.KFM.stD x y).G rO)



/-- What the main computation reads from the registers. -/
structure BaseOK (t : IState HS) (n : ℕ) : Prop where
  lr : IntMul.OpenAI.R154.P.NLogN.KFM.LRegs t n
  dr : DescRegs t n (pP n + 2) rPw
  hS : Hold t NLogN.KFM.rS (sCmp n)
  hT : Hold t NLogN.KFM.rT (2 ^ IntMul.OpenAI.Glue.LP n)
  hT2 : Hold t rT2 (2 ^ (IntMul.OpenAI.Glue.LP n + 1))
  hM : Hold t NLogN.KFM.rM ((n + bP n - 1) / bP n : ℕ)
  hP2 : Hold t rP2 (2 ^ pP n)
  hG : Hold t rG (2 ^ (2 * IntMul.OpenAI.R154.dP n * αP n ^ 2))
  hE2 : Hold t rE2 (2 ^ (pP n - bP n - 2))
  hB2 : Hold t rB2 (2 ^ bP n)
  hZ : Hold t rZ (2 * ((sCmp n : ℤ) - ((n + bP n - 1) / bP n : ℕ)))
  hH : Hold t NLogN.KFM.rH (2 ^ (pP n - 1))
  hF : Hold t rF (2 ^ (2 * bP n + 4))
  hO : Hold t rO (2 ^ (2 * n))
  hOne : Hold t rOne 1

end IntMul.OpenAI.R154.P.NLogN.KFM

end

-- from K_Defs24
section

namespace IntMul.OpenAI.R154.P.NLogN.KFM
open _root_.NLogN hiding DE bitE fmB liftL parC
open _root_.IntMul.OpenAI.R154.P.NLogN
open _root_.NLogN.KFM hiding BaseOK BigCtx ChainSizes Close D18Regs DescRegs ErC EsN LRegs LineNeed NcN P18IL QRegs TrRegs bLn baseSt bigP bsN cLineU chirpGN descChirpN descLineN descPhiN dpN gapR kBigF kChirp kDig kFin kFinA kFt kFtF kGm kIn kInF kLine kMul kPhi kRd kShF kShl kSm lineG muN parQV prodN sB sBD sCmp setC setP setupA setupS setupSt srcN stD tB tBD tF tsN ubar wFR wU zsWf
open _root_.IntMul.OpenAI.R154.P.NLogN.KFM

open _root_.IntMul
open _root_.NLogN.KIL hiding Cfg FR St aE aK cMv cStep cstep gS negP outR pT padL rJ1 rS rT sI stD tB zB zR
open _root_.NLogN.KFB hiding permL permP rB2 rG rN
open _root_.IntMul.HvdH
open _root_.IntMul.OpenAI.RT
open _root_.IntMul.OpenAI.Glue hiding KP dP rP αP γP ℓP
open _root_.IntMul.OpenAI.R154

noncomputable section

/-- The padded box formula. -/
def tF (n : ℕ) (j : ℕ) : ℕ := if dpN n ≤ j then IntMul.OpenAI.R154.rP n else IntMul.OpenAI.R154.rP n / 2

/-- The body of `LineNeed` for `n`, in dimension `d`. -/
def lineG {E : ℕ} (Isym : List Sym) (ext : Fin E → IStmt HS (7 + E)) (eA eB : Fin (7 + E))
    (dS : Fin HS) (C₀ : ℝ) (A n d : ℕ) : Prop :=
  ∀ [∀ i : Fin d, NeZero (srcN n i)] [∀ i : Fin d, NeZero (IntMul.OpenAI.R154.P.NLogN.KFM.tF n i)],
  ∀ (s : IState HS) (f : Fin HS → List ℤ) (l : List ℤ),
    (∀ j, j ≠ 0 → j ≠ dS → f j = []) →
    f dS = descLineN n →
    (∀ (zs : List GI) (u : ((i : Fin d) → ZMod (srcN n i)) → ℂ),
      f 0 = gflat zs ++ l → RepPad (pP n) (fun i : Fin d => srcN n i) (fun i : Fin d => IntMul.OpenAI.R154.P.NLogN.KFM.tF n i) zs u →
      ‖u‖ ≤ 1 / 2 →
      ∃ (zs' : List GI) (w : ((i : Fin d) → ZMod (IntMul.OpenAI.R154.P.NLogN.KFM.tF n i)) → ℂ) (c : ℕ),
        IRuns Isym (kTable ext) (.call eA) (NLogN.KIL.encK s f)
          (NLogN.KIL.encK s (Function.update f 0 (gflat zs' ++ l))) c ∧
        RepFull (pP n) (fun i : Fin d => IntMul.OpenAI.R154.P.NLogN.KFM.tF n i) zs' w ∧ NLogN.KFB.GB (pP n + 2) zs' ∧
        (∀ M : AxisMaps (d := d) (pP n) (αP n) (fun i : Fin d => srcN n i) (fun i : Fin d => IntMul.OpenAI.R154.P.NLogN.KFM.tF n i),
          ‖w - tensCLM (kerA M.A) u‖ ≤ epsA (pP n) (αP n) d * hp (pP n)) ∧
        (c : ℝ) ≤ C₀ * cLineU n A) ∧
    (∀ (ys : List GI) (y : ((i : Fin d) → ZMod (IntMul.OpenAI.R154.P.NLogN.KFM.tF n i)) → ℂ),
      f 0 = gflat ys ++ l → RepFull (pP n) (fun i : Fin d => IntMul.OpenAI.R154.P.NLogN.KFM.tF n i) ys y → ‖y‖ ≤ 1 →
      ∃ (ys' : List GI) (v : ((i : Fin d) → ZMod (srcN n i)) → ℂ) (c : ℕ),
        IRuns Isym (kTable ext) (.call eB) (NLogN.KIL.encK s f)
          (NLogN.KIL.encK s (Function.update f 0 (gflat ys' ++ l))) c ∧
        RepPad (pP n) (fun i : Fin d => srcN n i) (fun i : Fin d => IntMul.OpenAI.R154.P.NLogN.KFM.tF n i) ys' v ∧
        NLogN.KFB.GB (pP n + 2) ys' ∧
        (∀ M : AxisMaps (d := d) (pP n) (αP n) (fun i : Fin d => srcN n i) (fun i : Fin d => IntMul.OpenAI.R154.P.NLogN.KFM.tF n i),
          ‖v - tensCLM (kerB M.B) y‖ ≤
            epsB (pP n) (αP n) (fun i : Fin d => srcN n i) (fun i : Fin d => IntMul.OpenAI.R154.P.NLogN.KFM.tF n i) * hp (pP n)) ∧
        (c : ℝ) ≤ C₀ * cLineU n A)

end

end IntMul.OpenAI.R154.P.NLogN.KFM

end

-- from K_Defs24
section

set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false

namespace IntMul.OpenAI.R154.P.NLogN.KFM
open _root_.NLogN hiding DE bitE fmB liftL parC
open _root_.IntMul.OpenAI.R154.P.NLogN
open _root_.NLogN.KFM hiding BaseOK BigCtx ChainSizes Close D18Regs DescRegs ErC EsN LRegs LineNeed NcN P18IL QRegs TrRegs bLn baseSt bigP bsN cLineU chirpGN descChirpN descLineN descPhiN dpN gapR kBigF kChirp kDig kFin kFinA kFt kFtF kGm kIn kInF kLine kMul kPhi kRd kShF kShl kSm lineG muN parQV prodN sB sBD sCmp setC setP setupA setupS setupSt srcN stD tB tBD tF tsN ubar wFR wU zsWf
open _root_.IntMul.OpenAI.R154.P.NLogN.KFM

open _root_.AModel hiding hdPos
open _root_.AModelL12
open _root_.IntMul
open _root_.NLogN.KIL hiding Cfg FR St aE aK cMv cStep cstep gS negP outR pT padL rJ1 rS rT sI stD tB zB zR
open _root_.NLogN.KFB hiding permL permP rB2 rG rN
open _root_.NLogN.KFT hiding carW tE zB
open _root_.NLogN.RS
open _root_.IntMul.HvdH
open _root_.IntMul.OpenAI.RT
open _root_.IntMul.OpenAI.RC
open _root_.IntMul.OpenAI.Glue hiding KP dP rP αP γP ℓP
open _root_.IntMul.OpenAI.R154
open _root_.IntMul.OpenAI.RCost hiding Ncost c es lam' δ ε κ τ
open _root_.IntMul.OpenAI.R154

noncomputable section





section Call

variable {P P' : ℕ} {I : List Sym} {iprog : Fin P → IStmt HS P} {iprog' : Fin P' → IStmt HS P'}
  {g : Fin P' → Fin P}


end Call


section Phases

variable {P P' : ℕ} {Isym : List Sym} {iprog : Fin P → IStmt HS P}
  {ext : Fin P' → IStmt HS (7 + P')} {g : Fin (7 + P') → Fin P}
  (hprog : ∀ j, iprog (g j) = (kTable ext j).ren id g)
  {n D : ℕ} (hn : n0 ≤ n) (hD : dP n = D + 1)

/-- The cost bound of a line call. -/
def kLine (n Bd : ℕ) (C₀ : ℝ) (A : ℕ) : ℝ :=
  1 + 2 * 10 ^ 12 * (bP n + 1) ^ 3 + 3 * (descLineN n).length * cMv Bd + 101 + C₀ * cLineU n A

/-- The cost bound of a chirp call. -/
def kChirp (n Bd : ℕ) (C₀ : ℝ) (A : ℕ) : ℝ :=
  1 + 3 * 10 ^ 12 * (bP n + 1) ^ 3 + 3 * (descChirpN n).length * cMv Bd + 101 + C₀ * cLineU n A

/-- The chirp guarantee for fixed tables (the body of `ChirpNeedR` after the tables). -/
def chirpGN (Isym : List Sym) (ext : Fin P' → IStmt HS (7 + P')) (eC : Fin (7 + P')) (dS : Fin HS)
    (C₀ : ℝ) (A n D : ℕ) [∀ i, NeZero (tBD n D i)]
    (θt θit at' bt : ((i : Fin (D + 1)) → ZMod (tBD n D i)) → ℂ) : Prop :=
  ∀ (s : IState HS) (f : Fin HS → List ℤ) (l : List ℤ),
    (∀ j, j ≠ 0 → j ≠ dS → f j = []) →
    f dS = descChirpN n →
    ∀ (xs : List GI) (x : ((i : Fin (D + 1)) → ZMod (tBD n D i)) → ℂ),
      f 0 = gflat xs ++ l → RepFull (pP n) (tBD n D) xs x → ‖x‖ ≤ 6 / 10 →
      ∃ (Mrt : (((i : Fin (D + 1)) → ZMod (tBD n D i)) → ℂ) →
          (((i : Fin (D + 1)) → ZMod (tBD n D i)) → ℂ) →
          (((i : Fin (D + 1)) → ZMod (tBD n D i)) → ℂ)),
        (∀ f g, Grid (pP n) f → Grid (pP n) g → ‖f‖ ≤ 1 → ‖g‖ ≤ 1 →
          ‖Mrt f g - mrX (tBD n D) f g‖ ≤ ErC n D * hp (pP n)) ∧
      ∃ (ys : List GI) (c : ℕ),
        IRuns Isym (kTable ext) (.call eC) (NLogN.KIL.encK s f)
          (NLogN.KIL.encK s (Function.update f 0 (gflat ys ++ l))) c ∧
        RepFull (pP n) (tBD n D) ys (chirpT (pP n) (mcT (pP n) Mrt θt θit) bt at' x) ∧
        NLogN.KFB.GB (pP n + 2) ys ∧
        (c : ℝ) ≤ C₀ * cLineU n A


/-- The descriptor of `Φ` for `n`. -/
def descPhiN (n : ℕ) : List ℤ :=
  descPhi (pP n + 2) (ℓP n - 1) (IntMul.OpenAI.R154.dP n) (bLn n) (srcN n) (muN n)

/-- The cost bound of a `Φ` call. -/
def kPhi (n Bd : ℕ) (C₀ : ℝ) : ℝ :=
  1 + 2 * 10 ^ 13 * (bP n + 1) ^ 3 * (bP n + IntMul.OpenAI.R154.rP n + 5) + 3 * (descPhiN n).length * cMv Bd + 101 +
    C₀ * cPhiU (pP n + 2) (ℓP n - 1) (IntMul.OpenAI.R154.dP n) (bLn n) (srcN n)

end Phases

end

end IntMul.OpenAI.R154.P.NLogN.KFM

end

-- from K_Defs24
section

namespace IntMul.OpenAI.R154.P.NLogN.KFM
open _root_.NLogN hiding DE bitE fmB liftL parC
open _root_.IntMul.OpenAI.R154.P.NLogN
open _root_.NLogN.KFM hiding BaseOK BigCtx ChainSizes Close D18Regs DescRegs ErC EsN LRegs LineNeed NcN P18IL QRegs TrRegs bLn baseSt bigP bsN cLineU chirpGN descChirpN descLineN descPhiN dpN gapR kBigF kChirp kDig kFin kFinA kFt kFtF kGm kIn kInF kLine kMul kPhi kRd kShF kShl kSm lineG muN parQV prodN sB sBD sCmp setC setP setupA setupS setupSt srcN stD tB tBD tF tsN ubar wFR wU zsWf
open _root_.IntMul.OpenAI.R154.P.NLogN.KFM

open _root_.IntMul
open _root_.NLogN.KIL hiding Cfg FR St aE aK cMv cStep cstep gS negP outR pT padL rJ1 rS rT sI stD tB zB zR
open _root_.NLogN.KFB hiding permL permP rB2 rG rN
open _root_.IntMul.HvdH
open _root_.IntMul.OpenAI.RT
open _root_.IntMul.OpenAI.RC
open _root_.IntMul.OpenAI.Glue hiding KP dP rP αP γP ℓP
open _root_.IntMul.OpenAI.R154

noncomputable section

/-- **The parameter sizes** (hypothesis of the assembly). -/
def ChainSizes : Prop :=
  ∃ n₂ : ℕ, ∀ n, IntMul.OpenAI.Glue.n0 ≤ n → n₂ ≤ n → ∀ D, IntMul.OpenAI.R154.dP n = D + 1 →
    -- axes
    (∀ i, 2 ≤ sBD n D i) ∧ (∀ i, sBD n D i < tBD n D i) ∧ (∀ i, Even (tBD n D i)) ∧
    (∀ i, Nat.Coprime (sBD n D i) (tBD n D i)) ∧
    (∀ i j, i ≠ j → Nat.Coprime (sBD n D i) (sBD n D j)) ∧
    -- Lemma 19 per axis (`axisMaps_exists`)
    2 ≤ αP n ∧ αP n ^ 2 ≤ pP n ∧
    (∀ i, sBD n D i ≤ αP n ^ 2 * (tBD n D i - sBD n D i)) ∧
    (∀ i, 100 * (jIter (pP n) (sBD n D i) (tBD n D i) (αP n) *
      (10 * eWidth (pP n) (αP n) + 12) + 1) ≤ 2 ^ pP n) ∧
    4 * (6 * sWidth (pP n) (αP n) + 4) ≤ 2 ^ pP n ∧
    -- `chain_concrete`
    epsA (pP n) (αP n) (D + 1) * hp (pP n) ≤ 1 / 10 ∧
    ErC n D * hp (pP n) ≤ 1 / 10 ∧
    (2 : ℝ) ^ (2 * (D + 1) * αP n ^ 2) * ((epsA (pP n) (αP n) (D + 1) + (ErC n D + 22) +
      epsB (pP n) (αP n) (sBD n D) (tBD n D)) * hp (pP n)) ≤ 1 / 100 ∧
    2 * (2 : ℝ) ^ (2 * bP n + 4) * (∏ i, (sBD n D i : ℝ)) ^ 2 *
      (3 * ((2 : ℝ) ^ (2 * (D + 1) * αP n ^ 2) * (epsA (pP n) (αP n) (D + 1) + (ErC n D + 22) +
        epsB (pP n) (αP n) (sBD n D) (tBD n D))) + 2) * hp (pP n) < 1 ∧
    -- digits
    bP n + 2 ≤ pP n ∧ 2 * ((n + bP n - 1) / bP n) ≤ ∏ i, sBD n D i

end

end IntMul.OpenAI.R154.P.NLogN.KFM

end

-- from K_Defs24
section

set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false

namespace IntMul.OpenAI.R154.P.NLogN.KFM
open _root_.NLogN hiding DE bitE fmB liftL parC
open _root_.IntMul.OpenAI.R154.P.NLogN
open _root_.NLogN.KFM hiding BaseOK BigCtx ChainSizes Close D18Regs DescRegs ErC EsN LRegs LineNeed NcN P18IL QRegs TrRegs bLn baseSt bigP bsN cLineU chirpGN descChirpN descLineN descPhiN dpN gapR kBigF kChirp kDig kFin kFinA kFt kFtF kGm kIn kInF kLine kMul kPhi kRd kShF kShl kSm lineG muN parQV prodN sB sBD sCmp setC setP setupA setupS setupSt srcN stD tB tBD tF tsN ubar wFR wU zsWf
open _root_.IntMul.OpenAI.R154.P.NLogN.KFM

open _root_.AModel hiding hdPos
open _root_.AModelL12
open _root_.IntMul
open _root_.NLogN.KIL hiding Cfg FR St aE aK cMv cStep cstep gS negP outR pT padL rJ1 rS rT sI stD tB zB zR
open _root_.NLogN.KFB hiding permL permP rB2 rG rN
open _root_.NLogN.KFT hiding carW tE zB
open _root_.NLogN.RS
open _root_.IntMul.HvdH
open _root_.IntMul.OpenAI.RT
open _root_.IntMul.OpenAI.RC
open _root_.IntMul.OpenAI.Glue hiding KP dP rP αP γP ℓP
open _root_.IntMul.OpenAI.R154
open _root_.IntMul.OpenAI.RCost hiding Ncost c es lam' δ ε κ τ
open _root_.IntMul.OpenAI.R154

noncomputable section


/-- The error constant of one source transform. -/
def EsN (n D : ℕ) : ℝ :=
  (2 : ℝ) ^ (2 * (D + 1) * αP n ^ 2) * (epsA (pP n) (αP n) (D + 1) + (ErC n D + 22) +
    epsB (pP n) (αP n) (sBD n D) (tBD n D))

/-- The cost bound of the shift pass. -/
def kShl (n D : ℕ) : ℕ :=
  cItem (2 ^ (IntMul.OpenAI.Glue.LP n + 1)) (1000 * (pP n + 2 + 2 * (D + 1) * αP n ^ 2 + 2))
      (pP n + 2 + 2 * (D + 1) * αP n ^ 2 + 1) + 2 * cCnt (2 ^ (IntMul.OpenAI.Glue.LP n + 1)) +
    cW (2 ^ (2 * (D + 1) * αP n ^ 2)) + cW ((2 ^ (IntMul.OpenAI.Glue.LP n + 1) : ℕ) : ℤ)

section Ftil

variable {P P₂ P₃ : ℕ} {Isym : List Sym} {iprog : Fin P → IStmt HS P}
  {ext₂ : Fin P₂ → IStmt HS (7 + P₂)} {g₂ : Fin (7 + P₂) → Fin P}
  {ext₃ : Fin P₃ → IStmt HS (7 + P₃)} {g₃ : Fin (7 + P₃) → Fin P}


end Ftil

end

end IntMul.OpenAI.R154.P.NLogN.KFM

end

-- from K_Defs24
section

set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
set_option maxRecDepth 20000

namespace IntMul.OpenAI.R154.P.NLogN.KFM
open _root_.NLogN hiding DE bitE fmB liftL parC
open _root_.IntMul.OpenAI.R154.P.NLogN
open _root_.NLogN.KFM hiding BaseOK BigCtx ChainSizes Close D18Regs DescRegs ErC EsN LRegs LineNeed NcN P18IL QRegs TrRegs bLn baseSt bigP bsN cLineU chirpGN descChirpN descLineN descPhiN dpN gapR kBigF kChirp kDig kFin kFinA kFt kFtF kGm kIn kInF kLine kMul kPhi kRd kShF kShl kSm lineG muN parQV prodN sB sBD sCmp setC setP setupA setupS setupSt srcN stD tB tBD tF tsN ubar wFR wU zsWf
open _root_.IntMul.OpenAI.R154.P.NLogN.KFM

open _root_.AModel hiding hdPos
open _root_.AModelL12
open _root_.IntMul
open _root_.NLogN.KIL hiding Cfg FR St aE aK cMv cStep cstep gS negP outR pT padL rJ1 rS rT sI stD tB zB zR
open _root_.NLogN.KFB hiding permL permP rB2 rG rN
open _root_.NLogN.KFT hiding carW tE zB
open _root_.NLogN.KFU hiding cMv oA oC oD zD
open _root_.NLogN.RS
open _root_.IntMul.HvdH
open _root_.IntMul.OpenAI.RT
open _root_.IntMul.OpenAI.RC
open _root_.IntMul.OpenAI.Glue hiding KP dP rP αP γP ℓP
open _root_.IntMul.OpenAI.R154
open _root_.IntMul.OpenAI.RCost hiding Ncost c es lam' δ ε κ τ
open _root_.IntMul.OpenAI.R154

noncomputable section


/-- Everything the run for `n` uses. -/
structure BigCtx {E : ℕ} (ix : Ix (7 + E)) (Isym : List Sym) (extM : Fin E → IStmt HS (7 + E))
    (n D : ℕ) [∀ i, NeZero (sBD n D i)] [∀ i, NeZero (tBD n D i)] where
  hn : IntMul.OpenAI.Glue.n0 ≤ n
  hD : IntMul.OpenAI.R154.dP n = D + 1
  -- `Φ`
  ext₁ : Fin ix.P₁ → IStmt HS (7 + ix.P₁)
  hp₁ : ∀ j, kTable extM (ix.g₁ j) = (kTable ext₁ j).ren id ix.g₁
  CΦ : ℝ
  hdΦ : ix.dSΦ ≠ 0
  hΦ : phiG Isym ext₁ ix.eF ix.eI ix.dSΦ CΦ (pP n + 2) (ℓP n - 1) (IntMul.OpenAI.R154.dP n) (bLn n) (srcN n) (muN n)
  BΦ : ℕ
  hBΦ : ∀ x ∈ descPhiN n, zsz x ≤ BΦ
  -- lines
  ext₂ : Fin ix.P₂ → IStmt HS (7 + ix.P₂)
  hp₂ : ∀ j, kTable extM (ix.g₂ j) = (kTable ext₂ j).ren id ix.g₂
  CL : ℝ
  AL : ℕ
  hdL : ix.dSL ≠ 0
  hL : lineG Isym ext₂ ix.eA ix.eB ix.dSL CL AL n (D + 1)
  BL : ℕ
  hBL : ∀ x ∈ descLineN n, zsz x ≤ BL
  -- chirp
  ext₃ : Fin ix.P₃ → IStmt HS (7 + ix.P₃)
  hp₃ : ∀ j, kTable extM (ix.g₃ j) = (kTable ext₃ j).ren id ix.g₃
  CC : ℝ
  AC : ℕ
  hdC : ix.dSC ≠ 0
  θt : ((i : Fin (D + 1)) → ZMod (tBD n D i)) → ℂ
  θit : ((i : Fin (D + 1)) → ZMod (tBD n D i)) → ℂ
  at' : ((i : Fin (D + 1)) → ZMod (tBD n D i)) → ℂ
  bt : ((i : Fin (D + 1)) → ZMod (tBD n D i)) → ℂ
  ζ : ℂ
  hζ : ζ ^ tBD n D (Fin.last D) = -1
  hθ : Phases (pP n) (twX (tBD n D) ζ) θt
  hθi : Phases (pP n) (fun j => (twX (tBD n D) ζ j)⁻¹) θit
  ha : Phases (pP n) (fun j => (starRingEnd ℂ) (chirp (sBD n D) (tBD n D) j)) at'
  hb' : Phases (pP n) (chirp (sBD n D) (tBD n D)) bt
  hbg : Grid (pP n) bt
  hC : chirpGN Isym ext₃ ix.eC ix.dSC CC AC n D θt θit at' bt
  BC : ℕ
  hBC : ∀ x ∈ descChirpN n, zsz x ≤ BC
  -- sizes
  hlt : ∀ i, sBD n D i < tBD n D i
  ht : ∀ i, Even (tBD n D i)
  hcop : ∀ i, Nat.Coprime (sBD n D i) (tBD n D i)
  hpair : ∀ i j, i ≠ j → Nat.Coprime (sBD n D i) (sBD n D j)
  M : AxisMaps (d := D + 1) (pP n) (αP n) (sBD n D) (tBD n D)
  hεA : epsA (pP n) (αP n) (D + 1) * hp (pP n) ≤ 1 / 10
  hEr : ErC n D * hp (pP n) ≤ 1 / 10
  hEs : EsN n D * hp (pP n) ≤ 1 / 100
  hB2 : 2 * (2 : ℝ) ^ (2 * bP n + 4) * (∏ i, (sBD n D i : ℝ)) ^ 2 * (3 * EsN n D + 2) *
    hp (pP n) < 1
  hbp : bP n + 2 ≤ pP n
  hMS : 2 * ((n + bP n - 1) / bP n) ≤ ∏ i, sBD n D i
  H : CrtOK (D + 1) (srcN n) (muN n)






/-- The cost of the digit cut. -/
def kDig (n : ℕ) : ℕ :=
  cDigU (bP n) (NLogN.KFM.eN n) (NLogN.KFM.mN n) (sCmp n) + cW (2 ^ NLogN.KFM.eN n) + cW (((2 * (sCmp n - NLogN.KFM.mN n) : ℕ) : ℤ)) +
    cW (NLogN.KFM.mN n : ℤ) + cW (2 ^ bP n)

end

end IntMul.OpenAI.R154.P.NLogN.KFM

end

-- from K_Defs24
section

set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
set_option maxRecDepth 20000

namespace IntMul.OpenAI.R154.P.NLogN.KFM
open _root_.NLogN hiding DE bitE fmB liftL parC
open _root_.IntMul.OpenAI.R154.P.NLogN
open _root_.NLogN.KFM hiding BaseOK BigCtx ChainSizes Close D18Regs DescRegs ErC EsN LRegs LineNeed NcN P18IL QRegs TrRegs bLn baseSt bigP bsN cLineU chirpGN descChirpN descLineN descPhiN dpN gapR kBigF kChirp kDig kFin kFinA kFt kFtF kGm kIn kInF kLine kMul kPhi kRd kShF kShl kSm lineG muN parQV prodN sB sBD sCmp setC setP setupA setupS setupSt srcN stD tB tBD tF tsN ubar wFR wU zsWf
open _root_.IntMul.OpenAI.R154.P.NLogN.KFM

open _root_.AModel hiding hdPos
open _root_.AModelL12
open _root_.IntMul
open _root_.NLogN.KIL hiding Cfg FR St aE aK cMv cStep cstep gS negP outR pT padL rJ1 rS rT sI stD tB zB zR
open _root_.NLogN.KFB hiding permL permP rB2 rG rN
open _root_.NLogN.KFT hiding carW tE zB
open _root_.NLogN.KFU hiding cMv oA oC oD zD
open _root_.NLogN.RS
open _root_.IntMul.HvdH
open _root_.IntMul.OpenAI.RT
open _root_.IntMul.OpenAI.RC
open _root_.IntMul.OpenAI.Glue hiding KP dP rP αP γP ℓP
open _root_.IntMul.OpenAI.R154
open _root_.IntMul.OpenAI.RCost hiding Ncost c es lam' δ ε κ τ
open _root_.IntMul.OpenAI.R154

noncomputable section





variable {E : ℕ} {ix : Ix (7 + E)} {Isym : List Sym} {extM : Fin E → IStmt HS (7 + E)} {n D : ℕ}
  [instS : ∀ i, NeZero (sBD n D i)] [instT : ∀ i, NeZero (tBD n D i)]


/-- The digits `ū` of `x` on the box. -/
def ubar (C : BigCtx ix Isym extM n D) (x : ℕ) : ((i : Fin (D + 1)) → ZMod (sBD n D i)) → ℂ :=
  fun k => (dgt (bP n) (NLogN.KFM.mN n) x ((NLogN.KFM.eB (srcN n) (muN n) C.H).symm k).val : ℂ)

/-- The cost bound of one input. -/
def kIn (C : BigCtx ix Isym extM n D) : ℝ :=
  ((2 * moveCost (n + 1) + 19 + kDig n : ℕ) : ℝ) + kPhi n C.BΦ C.CΦ +
    (kLine n C.BL C.CL C.AL + kChirp n C.BC C.CC C.AC + kLine n C.BL C.CL C.AL + kShl n D)

end

end IntMul.OpenAI.R154.P.NLogN.KFM

end

-- from K_Defs24
section

set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
set_option maxRecDepth 20000

namespace IntMul.OpenAI.R154.P.NLogN.KFM
open _root_.NLogN hiding DE bitE fmB liftL parC
open _root_.IntMul.OpenAI.R154.P.NLogN
open _root_.NLogN.KFM hiding BaseOK BigCtx ChainSizes Close D18Regs DescRegs ErC EsN LRegs LineNeed NcN P18IL QRegs TrRegs bLn baseSt bigP bsN cLineU chirpGN descChirpN descLineN descPhiN dpN gapR kBigF kChirp kDig kFin kFinA kFt kFtF kGm kIn kInF kLine kMul kPhi kRd kShF kShl kSm lineG muN parQV prodN sB sBD sCmp setC setP setupA setupS setupSt srcN stD tB tBD tF tsN ubar wFR wU zsWf
open _root_.IntMul.OpenAI.R154.P.NLogN.KFM

open _root_.AModel hiding hdPos
open _root_.AModelL12
open _root_.IntMul
open _root_.NLogN.KIL hiding Cfg FR St aE aK cMv cStep cstep gS negP outR pT padL rJ1 rS rT sI stD tB zB zR
open _root_.NLogN.KFB hiding permL permP rB2 rG rN
open _root_.NLogN.KFT hiding carW tE zB
open _root_.NLogN.KFU hiding cMv oA oC oD zD
open _root_.NLogN.RS
open _root_.IntMul.HvdH
open _root_.IntMul.OpenAI.RT
open _root_.IntMul.OpenAI.RC
open _root_.IntMul.OpenAI.Glue hiding KP dP rP αP γP ℓP
open _root_.IntMul.OpenAI.R154
open _root_.IntMul.OpenAI.RCost hiding Ncost c es lam' δ ε κ τ
open _root_.IntMul.OpenAI.R154

noncomputable section


variable {E : ℕ} {ix : Ix (7 + E)} {Isym : List Sym} {extM : Fin E → IStmt HS (7 + E)} {n D : ℕ}
  [instS : ∀ i, NeZero (sBD n D i)] [instT : ∀ i, NeZero (tBD n D i)]

/-- The width of the transform outputs. -/
def wU (n D : ℕ) : ℕ := pP n + 2 + (2 * (D + 1) * αP n ^ 2 + 1)


/-- The cost of the Gaussian product pass. -/
def kGm (n D : ℕ) : ℕ :=
  2 ^ IntMul.OpenAI.Glue.LP n * (4 * fmB (2 * IntMul.OpenAI.R154.P.NLogN.KFM.wU n D)) + 10 ^ 6 * (2 ^ IntMul.OpenAI.Glue.LP n + 1) * (IntMul.OpenAI.R154.P.NLogN.KFM.wU n D + pP n + 1) +
    2 * cCnt (2 * 2 ^ IntMul.OpenAI.Glue.LP n) + cW (2 ^ pP n) + cW ((2 * 2 ^ IntMul.OpenAI.Glue.LP n : ℕ) : ℤ) + cW ((2 ^ IntMul.OpenAI.Glue.LP n : ℕ) : ℤ)


/-- The cost bound of one source transform. -/
def kFt (C : BigCtx ix Isym extM n D) : ℝ :=
  kLine n C.BL C.CL C.AL + kChirp n C.BC C.CC C.AC + kLine n C.BL C.CL C.AL + kShl n D

/-- The cost bound of the product phase. -/
def kMul (C : BigCtx ix Isym extM n D) : ℝ :=
  kIn C + ((2 * cMvN (2 ^ (IntMul.OpenAI.Glue.LP n + 1)) (IntMul.OpenAI.R154.P.NLogN.KFM.wU n D) : ℕ) : ℝ) + kIn C + (kGm n D : ℝ) +
    (kCj n (pP n + 1) : ℝ) + kFt C

end

end IntMul.OpenAI.R154.P.NLogN.KFM

end

-- from K_Defs24
section

set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false

namespace IntMul.OpenAI.R154.P.NLogN.KFM
open _root_.NLogN hiding DE bitE fmB liftL parC
open _root_.IntMul.OpenAI.R154.P.NLogN
open _root_.NLogN.KFM hiding BaseOK BigCtx ChainSizes Close D18Regs DescRegs ErC EsN LRegs LineNeed NcN P18IL QRegs TrRegs bLn baseSt bigP bsN cLineU chirpGN descChirpN descLineN descPhiN dpN gapR kBigF kChirp kDig kFin kFinA kFt kFtF kGm kIn kInF kLine kMul kPhi kRd kShF kShl kSm lineG muN parQV prodN sB sBD sCmp setC setP setupA setupS setupSt srcN stD tB tBD tF tsN ubar wFR wU zsWf
open _root_.IntMul.OpenAI.R154.P.NLogN.KFM

open Complex
open _root_.AModel hiding hdPos
open _root_.AModelL12
open _root_.IntMul
open _root_.NLogN.KIL hiding Cfg FR St aE aK cMv cStep cstep gS negP outR pT padL rJ1 rS rT sI stD tB zB zR
open _root_.NLogN.KFB hiding permL permP rB2 rG rN
open _root_.NLogN.KFT hiding carW tE zB
open _root_.NLogN.KFU hiding cMv oA oC oD zD
open _root_.NLogN.RS
open _root_.IntMul.HvdH
open _root_.IntMul.OpenAI.RT
open _root_.IntMul.OpenAI.RC
open _root_.IntMul.OpenAI.Glue hiding KP dP rP αP γP ℓP
open _root_.IntMul.OpenAI.R154
open _root_.IntMul.OpenAI.RCost hiding Ncost c es lam' δ ε κ τ
open _root_.IntMul.OpenAI.R154

noncomputable section



/-- The width of the rounding passes. -/
def wFR (n D : ℕ) : ℕ := IntMul.OpenAI.R154.P.NLogN.KFM.wU n D + 4 * bP n + 5


/-- The cost of one `×S` pass. -/
def kSm (n D : ℕ) : ℕ :=
  cItem (2 ^ (IntMul.OpenAI.Glue.LP n + 1)) (fmB (2 * wFR n D) + 5000 * (wFR n D + 0 + 3)) (2 * wFR n D) +
    2 * cCnt (2 ^ (IntMul.OpenAI.Glue.LP n + 1)) + cW (sCmp n : ℤ) + cW (2 ^ 0) + cW ((2 ^ (IntMul.OpenAI.Glue.LP n + 1) : ℕ) : ℤ)

/-- The cost of the `×2^{2b+4}` pass. -/
def kShF (n D : ℕ) : ℕ :=
  cItem (2 ^ (IntMul.OpenAI.Glue.LP n + 1)) (1000 * (wFR n D + (2 * bP n + 4) + 2)) (wFR n D + (2 * bP n + 4) + 1) +
    2 * cCnt (2 ^ (IntMul.OpenAI.Glue.LP n + 1)) + cW (2 ^ (2 * bP n + 4)) + cW ((2 ^ (IntMul.OpenAI.Glue.LP n + 1) : ℕ) : ℤ)

/-- The cost of the rounding pass. -/
def kRd (n D : ℕ) : ℕ :=
  cItem (2 ^ (IntMul.OpenAI.Glue.LP n + 1)) (3000 * (wFR n D + pP n + 3)) (2 * wFR n D + 1) +
    2 * cCnt (2 ^ (IntMul.OpenAI.Glue.LP n + 1)) + cW (2 ^ (pP n - 1)) + cW (2 ^ pP n) +
    cW ((2 ^ (IntMul.OpenAI.Glue.LP n + 1) : ℕ) : ℤ)

/-- The cost of `finA`. -/
def kFinA (n D : ℕ) : ℕ := kCj n (IntMul.OpenAI.R154.P.NLogN.KFM.wU n D) + (kSm n D + (kSm n D + (kShF n D + kRd n D)))

end

end IntMul.OpenAI.R154.P.NLogN.KFM

end

-- from K_Defs25
section

set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
set_option maxRecDepth 20000

namespace IntMul.OpenAI.R154.P.NLogN.KFM
open _root_.NLogN hiding DE bitE fmB liftL parC
open _root_.IntMul.OpenAI.R154.P.NLogN
open _root_.NLogN.KFM hiding BaseOK BigCtx ChainSizes Close D18Regs DescRegs ErC EsN LRegs LineNeed NcN P18IL QRegs TrRegs bLn baseSt bigP bsN cLineU chirpGN descChirpN descLineN descPhiN dpN gapR kBigF kChirp kDig kFin kFinA kFt kFtF kGm kIn kInF kLine kMul kPhi kRd kShF kShl kSm lineG muN parQV prodN sB sBD sCmp setC setP setupA setupS setupSt srcN stD tB tBD tF tsN ubar wFR wU zsWf
open _root_.IntMul.OpenAI.R154.P.NLogN.KFM

open Finset
open _root_.AModel hiding hdPos
open _root_.AModelL12
open _root_.IntMul
open _root_.NLogN.KIL hiding Cfg FR St aE aK cMv cStep cstep gS negP outR pT padL rJ1 rS rT sI stD tB zB zR
open _root_.NLogN.KFB hiding permL permP rB2 rG rN
open _root_.NLogN.KFT hiding carW tE zB
open _root_.NLogN.KFU hiding cMv oA oC oD zD
open _root_.NLogN.RS
open _root_.IntMul.HvdH
open _root_.IntMul.OpenAI.RT
open _root_.IntMul.OpenAI.RC
open _root_.IntMul.OpenAI.Glue hiding KP dP rP αP γP ℓP
open _root_.IntMul.OpenAI.R154
open _root_.IntMul.OpenAI.RCost hiding Ncost c es lam' δ ε κ τ
open _root_.IntMul.OpenAI.R154

noncomputable section


variable {E : ℕ} {ix : Ix (7 + E)} {Isym : List Sym} {extM : Fin E → IStmt HS (7 + E)} {n D : ℕ}
  [instS : ∀ i, NeZero (sBD n D i)] [instT : ∀ i, NeZero (tBD n D i)]

/-- The final closeness (the conclusion of `final_call3`). -/
def Close (C : BigCtx ix Isym extM n D) (x y : ℕ) (Z : ((i : Fin (D + 1)) → ZMod (sBD n D i)) → ℂ) :
    Prop :=
  ∀ j, ‖(2 : ℂ) ^ (2 * bP n + 4) * ((∏ i, (sBD n D i : ℝ) : ℝ) : ℂ) *
      (((∏ i, (sBD n D i : ℝ) : ℝ) : ℂ) * cnj Z j) - cconv (sBD n D) (ubar C x) (ubar C y) j‖ <
    1 / 2

/-- The rounded array. -/
def zsWf (n : ℕ) (zsZ : List GI) : List GI :=
  (zsZ.map NLogN.KFM.gconj).map fun z => (rndV (pP n) (bP n) (sCmp n) z.1, rndV (pP n) (bP n) (sCmp n) z.2)




/-- The cost bound of the read-out. -/
def kFin (C : BigCtx ix Isym extM n D) : ℝ :=
  (kFinA n D : ℝ) + kPhi n C.BΦ C.CΦ +
    ((cCarU (bP n) (pP n + 2) (sCmp n) + cW (sCmp n : ℤ) + cW (2 ^ bP n) + outRCost (2 * n) : ℕ) : ℝ)

end

end IntMul.OpenAI.R154.P.NLogN.KFM

end

-- from K_Defs25
section

set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
set_option maxRecDepth 20000

namespace IntMul.OpenAI.R154.P.NLogN.KFM
open _root_.NLogN hiding DE bitE fmB liftL parC
open _root_.IntMul.OpenAI.R154.P.NLogN
open _root_.NLogN.KFM hiding BaseOK BigCtx ChainSizes Close D18Regs DescRegs ErC EsN LRegs LineNeed NcN P18IL QRegs TrRegs bLn baseSt bigP bsN cLineU chirpGN descChirpN descLineN descPhiN dpN gapR kBigF kChirp kDig kFin kFinA kFt kFtF kGm kIn kInF kLine kMul kPhi kRd kShF kShl kSm lineG muN parQV prodN sB sBD sCmp setC setP setupA setupS setupSt srcN stD tB tBD tF tsN ubar wFR wU zsWf
open _root_.IntMul.OpenAI.R154.P.NLogN.KFM

open Finset
open _root_.AModel hiding hdPos
open _root_.AModelL12
open _root_.IntMul
open _root_.NLogN.KIL hiding Cfg FR St aE aK cMv cStep cstep gS negP outR pT padL rJ1 rS rT sI stD tB zB zR
open _root_.NLogN.KFB hiding permL permP rB2 rG rN
open _root_.NLogN.KFT hiding carW tE zB
open _root_.NLogN.KFU hiding cMv oA oC oD zD
open _root_.NLogN.RS
open _root_.IntMul.HvdH
open _root_.IntMul.OpenAI.RT
open _root_.IntMul.OpenAI.RC
open _root_.IntMul.OpenAI.Glue hiding KP dP rP αP γP ℓP
open _root_.IntMul.OpenAI.R154
open _root_.IntMul.OpenAI.RCost hiding Ncost c es lam' δ ε κ τ
open _root_.IntMul.OpenAI.R154

noncomputable section

variable {E : ℕ} {ix : Ix (7 + E)} {Isym : List Sym} {extM : Fin E → IStmt HS (7 + E)} {n D : ℕ}
  [instS : ∀ i, NeZero (sBD n D i)] [instT : ∀ i, NeZero (tBD n D i)]

/-- **The program `bigE`.** -/
def bigP (ix : Ix (7 + E)) : IStmt HS (7 + E) := .seq setP (.seq (mulP ix) (finP ix))

/-- The setup cost as computed. -/
def setC (x y : List Bool) : ℕ :=
  cStart x.length + 12 * 10 ^ 15 * (bP x.length + 1) ^ 4 +
    parS.cost (setupSt x.length (stA x y)) +
    parQ.cost ((setupSt x.length (stA x y)).upd NLogN.KFM.rS (.int (sCmp x.length : ℤ) ::
      (setupSt x.length (stA x y)).G NLogN.KFM.rS)) + (3 + 2 * shlCost x.length)

end

end IntMul.OpenAI.R154.P.NLogN.KFM

end

-- from K_Defs25
section

set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
set_option maxRecDepth 20000

namespace IntMul.OpenAI.R154.P.NLogN.KFM
open _root_.NLogN hiding DE bitE fmB liftL parC
open _root_.IntMul.OpenAI.R154.P.NLogN
open _root_.NLogN.KFM hiding BaseOK BigCtx ChainSizes Close D18Regs DescRegs ErC EsN LRegs LineNeed NcN P18IL QRegs TrRegs bLn baseSt bigP bsN cLineU chirpGN descChirpN descLineN descPhiN dpN gapR kBigF kChirp kDig kFin kFinA kFt kFtF kGm kIn kInF kLine kMul kPhi kRd kShF kShl kSm lineG muN parQV prodN sB sBD sCmp setC setP setupA setupS setupSt srcN stD tB tBD tF tsN ubar wFR wU zsWf
open _root_.IntMul.OpenAI.R154.P.NLogN.KFM

open Finset
open _root_.AModel hiding hdPos
open _root_.AModelL12
open _root_.IntMul
open _root_.NLogN.KIL hiding Cfg FR St aE aK cMv cStep cstep gS negP outR pT padL rJ1 rS rT sI stD tB zB zR
open _root_.NLogN.KFB hiding permL permP rB2 rG rN
open _root_.NLogN.KFT hiding carW tE zB
open _root_.NLogN.KFU hiding cMv oA oC oD zD
open _root_.NLogN.RS
open _root_.IntMul.HvdH
open _root_.IntMul.OpenAI.RT
open _root_.IntMul.OpenAI.RC
open _root_.IntMul.OpenAI.Glue hiding KP dP rP αP γP ℓP
open _root_.IntMul.OpenAI.R154
open _root_.IntMul.OpenAI.RCost hiding Ncost c es lam' δ ε κ τ
open _root_.IntMul.OpenAI.R154

noncomputable section





section Merge

variable {E₁ E₂ E₃ : ℕ}


end Merge


/-- `kIn` / `kFt` from the constants. -/
def kFtF (n D BL BC AL AC : ℕ) (CL CC : ℝ) : ℝ :=
  kLine n BL CL AL + kChirp n BC CC AC + kLine n BL CL AL + kShl n D

def kInF (n D BΦ BL BC AL AC : ℕ) (CΦ CL CC : ℝ) : ℝ :=
  ((2 * moveCost (n + 1) + 19 + kDig n : ℕ) : ℝ) + kPhi n BΦ CΦ + kFtF n D BL BC AL AC CL CC

/-- `kMul + kFin` from the constants. -/
def kBigF (n D BΦ BL BC AL AC : ℕ) (CΦ CL CC : ℝ) : ℝ :=
  (kInF n D BΦ BL BC AL AC CΦ CL CC + ((2 * cMvN (2 ^ (IntMul.OpenAI.Glue.LP n + 1)) (IntMul.OpenAI.R154.P.NLogN.KFM.wU n D) : ℕ) : ℝ) +
    kInF n D BΦ BL BC AL AC CΦ CL CC + (kGm n D : ℝ) + (kCj n (pP n + 1) : ℝ) +
    kFtF n D BL BC AL AC CL CC) +
  ((kFinA n D : ℝ) + kPhi n BΦ CΦ +
    ((cCarU (bP n) (pP n + 2) (sCmp n) + cW (sCmp n : ℤ) + cW (2 ^ bP n) + outRCost (2 * n) : ℕ) : ℝ))



end

end IntMul.OpenAI.R154.P.NLogN.KFM

end

-- from K_Defs25
section

set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false

namespace IntMul.OpenAI.R154.P.NLogN.KFM
open _root_.NLogN hiding DE bitE fmB liftL parC
open _root_.IntMul.OpenAI.R154.P.NLogN
open _root_.NLogN.KFM hiding BaseOK BigCtx ChainSizes Close D18Regs DescRegs ErC EsN LRegs LineNeed NcN P18IL QRegs TrRegs bLn baseSt bigP bsN cLineU chirpGN descChirpN descLineN descPhiN dpN gapR kBigF kChirp kDig kFin kFinA kFt kFtF kGm kIn kInF kLine kMul kPhi kRd kShF kShl kSm lineG muN parQV prodN sB sBD sCmp setC setP setupA setupS setupSt srcN stD tB tBD tF tsN ubar wFR wU zsWf
open _root_.IntMul.OpenAI.R154.P.NLogN.KFM

open Finset
open _root_.IntMul
open _root_.NLogN.KIL hiding Cfg FR St aE aK cMv cStep cstep gS negP outR pT padL rJ1 rS rT sI stD tB zB zR
open _root_.NLogN.KFB hiding permL permP rB2 rG rN
open _root_.NLogN.KFT hiding carW tE zB
open _root_.NLogN.KFU hiding cMv oA oC oD zD
open _root_.NLogN.RS
open _root_.IntMul.OpenAI.Glue hiding KP dP rP αP γP ℓP
open _root_.IntMul.OpenAI.R154
open _root_.IntMul.OpenAI.RCost hiding Ncost c es lam' δ ε κ τ
open _root_.IntMul.OpenAI.R154

noncomputable section



section Basic

variable {n : ℕ} (hn : n0 ≤ n)
include hn

end Basic



section Sizes

variable {n D : ℕ} (hn : n0 ≤ n) (hD : dP n = D + 1)
include hn hD

end Sizes


section Passes

variable {n D : ℕ} (hn : n0 ≤ n) (hD : dP n = D + 1)
include hn hD

end Passes


section Desc

variable {n : ℕ} (hn : n0 ≤ n)
include hn

end Desc



/-- The `Ncost` of `n`. -/
def NcN (n : ℕ) : ℝ := Ncost (6 * (lg n : ℝ)) (IntMul.OpenAI.R154.dP n) (KP n) (ℓP n) (αP n)


end

end IntMul.OpenAI.R154.P.NLogN.KFM

end

-- from K_Defs25
section

set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
set_option linter.unusedSectionVars false

namespace IntMul.OpenAI.R154.P.NLogN.KFZ
open _root_.NLogN hiding St T1 T2 T3 T4 T5 T6 T7 tE
open _root_.IntMul.OpenAI.R154.P.NLogN
open _root_.NLogN.KFZ hiding BN ChirpNeedR bitN bsN hN length_bsN length_ssN ssN σN
open _root_.IntMul.OpenAI.R154.P.NLogN.KFZ

open _root_.IntMul
open _root_.NLogN.KIL hiding Cfg FR St aE cBody negP outR padL pushF pushes
open _root_.NLogN.KFB hiding permL permP qA qT
open _root_.NLogN.KFM hiding BaseOK BigCtx ChainSizes Close D18Regs DE DescRegs ErC EsN LRegs LineNeed NcN P18IL QRegs TrRegs bLn baseSt bigP bitE bsN cLineU chirpGN descChirpN descLineN descPhiN dpN eB eN fmB gapR gconj kBigF kChirp kDig kFin kFinA kFt kFtF kGm kIn kInF kLine kMul kPhi kRd kShF kShl kSm liftL lineG muN parC parQV prodN sB sBD sCmp setC setP setupA setupS setupSt srcN stD sumB tB tBD tF tsN ubar wFR wU zsWf
open _root_.IntMul.OpenAI.R154.P.NLogN.KFM
open _root_.IntMul.OpenAI.Glue hiding KP dP rP αP γP ℓP
open _root_.IntMul.OpenAI.R154
open _root_.IntMul.OpenAI.RP

noncomputable section

/-- The bit of axis `j`. -/
def bitN (n j : ℕ) : ℕ := if dpN n ≤ j then 1 else 0

/-- The bit list. -/
def bsN (n : ℕ) : List ℕ := (List.range (IntMul.OpenAI.R154.dP n)).map (bitN n)

/-- The source list. -/
def ssN (n : ℕ) : List ℕ := (List.range (IntMul.OpenAI.R154.dP n)).map (srcN n)

/-- `h = ℓ - 1`. -/
def hN (n : ℕ) : ℕ := ℓP n - 1

/-- `σ = d - dpN`. -/
def σN (n : ℕ) : ℕ := IntMul.OpenAI.R154.dP n - dpN n

/-- The register width. -/
def BN (n : ℕ) : ℕ := dlV (pP n) (IntMul.OpenAI.R154.P.NLogN.KFZ.hN n) (IntMul.OpenAI.R154.dP n) + (IntMul.OpenAI.R154.dP n * IntMul.OpenAI.R154.P.NLogN.KFZ.hN n + σN n) + 8 + KP n + αP n + 1

section Facts

variable {n D : ℕ} (hn : n0 ≤ n) (hD : dP n = D + 1)
include hn hD

theorem length_bsN : (IntMul.OpenAI.R154.P.NLogN.KFZ.bsN n).length = D + 1 := by simp [IntMul.OpenAI.R154.P.NLogN.KFZ.bsN, hD]

theorem length_ssN : (ssN n).length = D + 1 := by simp [ssN, hD]

end Facts

end

end IntMul.OpenAI.R154.P.NLogN.KFZ

end

-- from K_Defs26
section

set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false

namespace IntMul.OpenAI.R154.P.NLogN.KFY
open _root_.NLogN hiding PB bitE mE passP tE
open _root_.IntMul.OpenAI.R154.P.NLogN
open _root_.NLogN.KFY hiding AN ArrInv AxBnd AxBndB AxF BN BaccN BoN BqN EN JbN NF NG QN ZN bN fsA fsB mN mainA mainB mmN overN srcsN tN ΦN

open _root_.IntMul
open _root_.IntMul.OpenAI.Glue hiding KP dP rP αP γP ℓP
open _root_.IntMul.OpenAI.R154
open _root_.IntMul.OpenAI.RP
open _root_.NLogN.KFM hiding BaseOK BigCtx ChainSizes Close D18Regs DE DescRegs ErC EsN LRegs LineNeed NcN P18IL QRegs TrRegs bLn baseSt bigP bitE bsN cLineU chirpGN dS descChirpN descLineN descPhiN dpN fmB gapR kBigF kChirp kDig kFin kFinA kFt kFtF kGm kIn kInF kLine kMul kPhi kRd kShF kShl kSm liftL lineG mN muN parC parQV prodN pushL sB sBD sCmp setC setP setupA setupS setupSt srcN stD tB tBD tF tsN ubar wFR wU zsWf
open _root_.IntMul.OpenAI.R154.P.NLogN.KFM

/-- The bit of axis `j`. -/
noncomputable def bN (n j : ℕ) : ℕ := if dpN n ≤ j then 1 else 0

end IntMul.OpenAI.R154.P.NLogN.KFY

end

-- from K_Defs26
section

set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
set_option linter.unusedSectionVars false

namespace IntMul.OpenAI.R154.P.NLogN.KFY
open _root_.NLogN hiding PB bitE mE passP tE
open _root_.IntMul.OpenAI.R154.P.NLogN
open _root_.NLogN.KFY hiding AN ArrInv AxBnd AxBndB AxF BN BaccN BoN BqN EN JbN NF NG QN ZN bN fsA fsB mN mainA mainB mmN overN srcsN tN ΦN
open _root_.IntMul.OpenAI.R154.P.NLogN.KFY

open _root_.IntMul
open _root_.NLogN hiding PB bitE mE passP tE
open _root_.IntMul.OpenAI.R154.P.NLogN
open _root_.IntMul.HvdH.Ref hiding bflyB bflyT dcomX dcomY difZ ditZ pmulZ
open _root_.NLogN.GL hiding imE reE rndE
open _root_.NLogN.AX hiding bN
open _root_.NLogN.Rsp hiding BN KN aE cE kE pSt spSt
open _root_.NLogN.KFM (shPad)
open _root_.IntMul.OpenAI.R154.P.NLogN.KFM (bsN)








/-- Size bounds for one axis (`A` pass). -/
structure AxBnd (n A B : ℕ) : Prop where
  env : KFM.CostEnv A B
  pA : 2 ^ (2 * IntMul.OpenAI.Glue.pP n) ≤ A
  αA : IntMul.OpenAI.R154.αP n ^ 2 * IntMul.OpenAI.R154.rP n ^ 2 ≤ A
  wA : IntMul.OpenAI.R154.rP n * (2 * HvdH.sWidth (IntMul.OpenAI.Glue.pP n) (IntMul.OpenAI.R154.αP n) + 1) + IntMul.OpenAI.R154.rP n ≤ A
  LA : 2 ^ IntMul.OpenAI.Glue.LP n ≤ A
  dA : IntMul.OpenAI.R154.dP n ≤ A
  pB : 2 * IntMul.OpenAI.Glue.pP n + 1 ≤ B
  LB : IntMul.OpenAI.Glue.LP n + 2 ≤ B

end IntMul.OpenAI.R154.P.NLogN.KFY

end

-- from K_Defs26
section

set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
set_option linter.unusedSectionVars false

namespace IntMul.OpenAI.R154.P.NLogN.KFY
open _root_.NLogN hiding PB bitE mE passP tE
open _root_.IntMul.OpenAI.R154.P.NLogN
open _root_.NLogN.KFY hiding AN ArrInv AxBnd AxBndB AxF BN BaccN BoN BqN EN JbN NF NG QN ZN bN fsA fsB mN mainA mainB mmN overN srcsN tN ΦN
open _root_.IntMul.OpenAI.R154.P.NLogN.KFY

open _root_.IntMul
open _root_.NLogN hiding PB bitE mE passP tE
open _root_.IntMul.OpenAI.R154.P.NLogN
open _root_.IntMul.HvdH.Ref hiding bflyB bflyT dcomX dcomY difZ ditZ pmulZ
open _root_.NLogN.GL hiding imE reE rndE
open _root_.NLogN.AX hiding bN
open _root_.NLogN.Rsp hiding BN KN aE cE kE pSt spSt


/-- The sources `s_0..s_{d−1}`. -/
noncomputable def srcsN (n : ℕ) : List ℤ := (List.range (IntMul.OpenAI.R154.dP n)).map fun j => (IntMul.OpenAI.R154.P.NLogN.KFM.srcN n j : ℤ)


end IntMul.OpenAI.R154.P.NLogN.KFY

end

-- from K_Defs26
section

set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
set_option linter.unusedSectionVars false

namespace IntMul.OpenAI.R154.P.NLogN.KFY
open _root_.NLogN hiding PB bitE mE passP tE
open _root_.IntMul.OpenAI.R154.P.NLogN
open _root_.NLogN.KFY hiding AN ArrInv AxBnd AxBndB AxF BN BaccN BoN BqN EN JbN NF NG QN ZN bN fsA fsB mN mainA mainB mmN overN srcsN tN ΦN
open _root_.IntMul.OpenAI.R154.P.NLogN.KFY

open _root_.IntMul
open _root_.NLogN hiding PB bitE mE passP tE
open _root_.IntMul.OpenAI.R154.P.NLogN
open _root_.IntMul.HvdH.Ref hiding bflyB bflyT dcomX dcomY difZ ditZ pmulZ
open _root_.NLogN.GL hiding imE reE rndE
open _root_.NLogN.AX hiding bN
open _root_.NLogN.Rsp hiding BN KN aE cE kE pSt spSt
open _root_.NLogN.KFM (shPad)
open _root_.IntMul.OpenAI.R154.P.NLogN.KFM (bsN)










/-- Size bounds for one axis (`B₀` pass). -/
structure AxBndB (n A B : ℕ) : Prop where
  env : KFM.CostEnv A B
  pA : 2 ^ (2 * IntMul.OpenAI.Glue.pP n) ≤ A
  αA : IntMul.OpenAI.R154.αP n ^ 2 * IntMul.OpenAI.R154.rP n ^ 2 ≤ A
  jA : IntMul.OpenAI.Glue.pP n * IntMul.OpenAI.R154.rP n + IntMul.OpenAI.R154.αP n ^ 2 * IntMul.OpenAI.R154.rP n ≤ A
  wA : IntMul.OpenAI.R154.rP n * (2 * HvdH.eWidth (IntMul.OpenAI.Glue.pP n) (IntMul.OpenAI.R154.αP n) + 1) + IntMul.OpenAI.R154.rP n ≤ A
  LA : 2 ^ IntMul.OpenAI.Glue.LP n ≤ A
  dA : IntMul.OpenAI.R154.dP n ≤ A
  pB : 2 * IntMul.OpenAI.Glue.pP n + 1 ≤ B
  LB : IntMul.OpenAI.Glue.LP n + 2 ≤ B


end IntMul.OpenAI.R154.P.NLogN.KFY

end

-- from K_Defs26
section

set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
set_option linter.unusedSectionVars false

namespace IntMul.OpenAI.R154.P.NLogN.KFY
open _root_.NLogN hiding PB bitE mE passP tE
open _root_.IntMul.OpenAI.R154.P.NLogN
open _root_.NLogN.KFY hiding AN ArrInv AxBnd AxBndB AxF BN BaccN BoN BqN EN JbN NF NG QN ZN bN fsA fsB mN mainA mainB mmN overN srcsN tN ΦN
open _root_.IntMul.OpenAI.R154.P.NLogN.KFY

open _root_.IntMul
open _root_.NLogN hiding PB bitE mE passP tE
open _root_.IntMul.OpenAI.R154.P.NLogN
open _root_.IntMul.HvdH.Ref hiding bflyB bflyT dcomX dcomY difZ ditZ pmulZ
open _root_.NLogN.GL hiding imE reE rndE
open _root_.NLogN.AX hiding bN
open _root_.NLogN.Rsp hiding BN KN aE cE kE pSt spSt


/-- `t_k`. -/
noncomputable def tN (n k : ℕ) : ℕ := 2 ^ (IntMul.OpenAI.R154.ℓP n - 1 + bN n k)
/-- `m_k = ∏_{i ≠ k} t_i`. -/
noncomputable def mN (n k : ℕ) : ℕ := 2 ^ (IntMul.OpenAI.Glue.LP n - (IntMul.OpenAI.R154.ℓP n - 1 + bN n k))

/-- The `A` line maps. -/
noncomputable def fsA (n : ℕ) (k : ℕ) : List KFB.GI → List KFB.GI :=
  sapL (IntMul.OpenAI.Glue.pP n) ((List.ofFn (IntMul.OpenAI.R154.P.NLogN.KFM.sB n)).getD k 1) ((List.ofFn (IntMul.OpenAI.R154.P.NLogN.KFM.tB n)).getD k 1) (IntMul.OpenAI.R154.αP n)

/-- The `B₀` line maps. -/
noncomputable def fsB (n : ℕ) (k : ℕ) : List KFB.GI → List KFB.GI :=
  b0Pad (IntMul.OpenAI.Glue.pP n) ((List.ofFn (IntMul.OpenAI.R154.P.NLogN.KFM.sB n)).getD k 1) ((List.ofFn (IntMul.OpenAI.R154.P.NLogN.KFM.tB n)).getD k 1) (IntMul.OpenAI.R154.αP n)

/-- The array invariant. -/
def ArrInv (n : ℕ) (X : List KFB.GI) : Prop :=
  X.length = (List.ofFn (IntMul.OpenAI.R154.P.NLogN.KFM.tB n)).prod ∧ DiscL (IntMul.OpenAI.Glue.pP n) X

end IntMul.OpenAI.R154.P.NLogN.KFY

end

-- from K_Defs26
section

set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
set_option linter.unusedSectionVars false

namespace IntMul.OpenAI.R154.P.NLogN.KFY
open _root_.NLogN hiding PB bitE mE passP tE
open _root_.IntMul.OpenAI.R154.P.NLogN
open _root_.NLogN.KFY hiding AN ArrInv AxBnd AxBndB AxF BN BaccN BoN BqN EN JbN NF NG QN ZN bN fsA fsB mN mainA mainB mmN overN srcsN tN ΦN
open _root_.IntMul.OpenAI.R154.P.NLogN.KFY

open _root_.IntMul
open _root_.NLogN hiding PB bitE mE passP tE
open _root_.IntMul.OpenAI.R154.P.NLogN
open _root_.IntMul.OpenAI.Glue hiding KP dP rP αP γP ℓP
open _root_.IntMul.OpenAI.R154
open _root_.NLogN.GL hiding imE reE rndE
open _root_.NLogN.AX hiding bN
open _root_.NLogN.Rsp hiding BN KN aE cE kE pSt spSt

noncomputable section

def JbN (n : ℕ) : ℕ := 4 * IntMul.OpenAI.R154.dP n * pP n / αP n ^ 2 + 1
def mmN (n : ℕ) : ℕ := 3 * pP n + 2 * lqN n + 4 + (2 * lqN n + 1) * JbN n
def BaccN (n : ℕ) : ℕ := 2 * mmN n + 4 * lqN n + ℓP n + 2 * pP n + 8
def BoN (n : ℕ) : ℕ := pP n + 2 + mmN n + 3 * lqN n
def QN (n : ℕ) : ℕ := BoN n + IntMul.OpenAI.Glue.LP n + ℓP n + 4
def BqN (n : ℕ) : ℕ := 24 * (ℓP n + 2 * lqN n + 4) + 2 * pP n + lqN n + 2
def EN (n : ℕ) : ℕ := 2 * pP n + IntMul.OpenAI.Glue.LP n + 2 * ℓP n + 2 * lqN n + 8
def AN (n : ℕ) : ℕ := 2 ^ EN n
def BN (n : ℕ) : ℕ := 8 * EN n + 1

def ΦN (n : ℕ) : ℕ := ΦF (2 * mmN n)



/-- The facts of `n` used by the parameter proofs. -/
structure NF (n : ℕ) : Prop where
  hn : IntMul.OpenAI.Glue.n0 ≤ n
  α2 : 2 ≤ αP n
  αp : αP n ^ 2 ≤ pP n
  d2 : 2 ≤ IntMul.OpenAI.R154.dP n
  win : ∀ k < IntMul.OpenAI.R154.dP n, 2 ≤ IntMul.OpenAI.R154.P.NLogN.KFM.srcN n k ∧ Odd (IntMul.OpenAI.R154.P.NLogN.KFM.srcN n k) ∧
    4 * IntMul.OpenAI.R154.dP n * IntMul.OpenAI.R154.P.NLogN.KFM.srcN n k ≤ (4 * IntMul.OpenAI.R154.dP n - 1) * tN n k


/-- The per-axis facts. -/
structure AxF (n k : ℕ) : Prop where
  s0 : 0 < IntMul.OpenAI.R154.P.NLogN.KFM.srcN n k
  st : IntMul.OpenAI.R154.P.NLogN.KFM.srcN n k < tN n k
  co : Nat.Coprime (IntMul.OpenAI.R154.P.NLogN.KFM.srcN n k) (tN n k)
  sw : IntMul.OpenAI.R154.P.NLogN.KFM.srcN n k ≤ 4 * IntMul.OpenAI.R154.dP n * (tN n k - IntMul.OpenAI.R154.P.NLogN.KFM.srcN n k)
  tr : tN n k ≤ 2 ^ ℓP n
  t2 : 2 ≤ tN n k
  J : HvdH.jIter (pP n) (IntMul.OpenAI.R154.P.NLogN.KFM.srcN n k) (tN n k) (αP n) ≤ JbN n



end

end IntMul.OpenAI.R154.P.NLogN.KFY

end

-- from K_Defs26
section

set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
set_option linter.unusedSectionVars false
set_option maxRecDepth 100000
set_option exponentiation.threshold 2048

namespace IntMul.OpenAI.R154.P.NLogN.KFY
open _root_.NLogN hiding PB bitE mE passP tE
open _root_.IntMul.OpenAI.R154.P.NLogN
open _root_.NLogN.KFY hiding AN ArrInv AxBnd AxBndB AxF BN BaccN BoN BqN EN JbN NF NG QN ZN bN fsA fsB mN mainA mainB mmN overN srcsN tN ΦN
open _root_.IntMul.OpenAI.R154.P.NLogN.KFY

open _root_.IntMul
open _root_.NLogN hiding PB bitE mE passP tE
open _root_.IntMul.OpenAI.R154.P.NLogN
open _root_.IntMul.OpenAI.Glue hiding KP dP rP αP γP ℓP
open _root_.IntMul.OpenAI.R154
open _root_.NLogN.GL hiding imE reE rndE
open _root_.NLogN.AX hiding bN
open _root_.NLogN.Rsp hiding BN KN aE cE kE pSt spSt

noncomputable section



/-- The facts of `n` used by the cost bounds. -/
structure NG (n : ℕ) : Prop where
  nf : NF n
  α4 : 12 * IntMul.OpenAI.R154.dP n ^ 2 * bP n ≤ αP n ^ 4
  bl : bP n ≤ 2 * IntMul.OpenAI.R154.dP n * ℓP n
  d5 : 2 ^ 18 * IntMul.OpenAI.R154.dP n ^ 5 ≤ bP n
  dbig : 2 ^ 12 ≤ IntMul.OpenAI.R154.dP n
  Lb : IntMul.OpenAI.Glue.LP n < bP n
  win2 : ∀ k < IntMul.OpenAI.R154.dP n, (4 * IntMul.OpenAI.R154.dP n - 2) * tN n k < 4 * IntMul.OpenAI.R154.dP n * IntMul.OpenAI.R154.P.NLogN.KFM.srcN n k

section facts

variable {n : ℕ} (h : NG n)
include h


end facts


section axis

variable {n : ℕ} (h : NG n) {k : ℕ} (hk : k < dP n)
include h hk

end axis


section sizes

variable {n : ℕ} (h : NG n)
include h


/-- The per-element factor. -/
def ZN (n : ℕ) : ℕ := ΦN n + mmN n + BaccN n + QN n + 2

end sizes


/-- The overhead collector. -/
def overN (n : ℕ) : ℕ := 10 ^ 80 * (pP n + 1) ^ 12 * (2 ^ ℓP n + 2) ^ 3

/-- The main term of an `A` axis. -/
def mainA (n : ℕ) : ℕ := 4 * 10 ^ 11 * (2 * HvdH.sWidth (pP n) (αP n) + 2) * 2 ^ IntMul.OpenAI.Glue.LP n * ZN n

/-- The main term of a `B₀` axis. -/
def mainB (n : ℕ) : ℕ :=
  9 * 10 ^ 14 * (JbN n + 1) * (2 * HvdH.eWidth (pP n) (αP n) + 2) * 2 ^ IntMul.OpenAI.Glue.LP n * ZN n

section axb

variable {n : ℕ} (h : NG n)
include h

end axb

section axis2

variable {n : ℕ} (h : NG n) {k : ℕ} (hk : k < dP n)
include h hk

end axis2


section pass

variable {n : ℕ} (h : NG n)
include h

end pass


end

end IntMul.OpenAI.R154.P.NLogN.KFY

end

-- from K_Defs27
section

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

namespace IntMul.OpenAI.R154.P.NLogN.KFV
open _root_.NLogN hiding posE tE twA twB vE zX
open _root_.IntMul.OpenAI.R154.P.NLogN
open _root_.NLogN.KFV hiding Cost18 EwB18 Log18Need P14Need P14Uat Par18Need cChunk total18

open _root_.IntMul
open _root_.NLogN.KFC hiding dbl enc encF mvB sT
open _root_.NLogN.KFT hiding tE
open _root_.NLogN.KFU hiding SwOK shR
open _root_.NLogN.KFB hiding blk permL permP
open _root_.NLogN.KFH hiding gD
open _root_.NLogN.KFD
open _root_.NLogN.KIL hiding Cfg FR St aE cBr cFwd cStep kG negP outR padL pre2 srcT swF yB
open _root_.AModel hiding blk hdPos
open _root_.Butterfly hiding Op



/-- **The uniform Proposition 14 KFV needs** (to be supplied by the KFW worker as `P14U`). -/
def P14Need {Pp : ℕ} (Isym : List Sym) (tbl : Fin Pp → IStmt HS Pp) (e14 : Fin Pp)
    (dS14 : Fin HS) (A : ℕ) (C₀ : ℝ) : Prop :=
  ∀ {K r Z P D S ρ p w : ℕ} (hρ : ρ < K),
    6 ≤ K → 1 ≤ r → 80 * Z * (Z + 2) ≤ 2 ^ K → 1 ≤ S → 1 ≤ P → 1 ≤ D →
    zsz ((32 * (vol (layerShape P K D S) * r) : ℕ) : ℤ) ≤ Z → zsz (p : ℤ) ≤ Z →
    (K : ℝ) ≤ 2 * (D : ℝ) ^ ((2 : ℝ)⁻¹ ^ 51) → KFM.EwB A D ≤ w + 1 → w + KFM.EwB A D + 2 < 2 ^ Z →
    2 * (2 * Z + 4) ^ 3 + 2 ≤ r → (K * D + P + 10) * (Z + 2) ≤ vol (layerShape P K D S) * r →
    ∀ (st : IState HS) (f : Fin HS → List ℤ) (zs : List GI) (l : List ℤ)
      (xs : List (Fin r → ℂ)), RecRep r p zs xs →
      xs.length = vol (layerShape P K D S) → f 0 = gflat zs ++ l →
      f dS14 = desc14 P K D S ρ r p w Z → (∀ j, p14Free dS14 j → f j = []) →
      NLogN.KFB.GB w zs → (∀ j (h : j < xs.length), ‖xs[j]‖ ≤ 1) →
      ∃ (zs' : List GI) (c : ℕ),
        RecRep r p zs' (prop14Proc (P := P) (S := S) hρ p (Butterfly.tens Cm : Butterfly.Op (Fin D)) xs) ∧
        NLogN.KFB.GB (p + 1) zs' ∧
        (∀ j (h : j < (prop14Proc (P := P) (S := S) hρ p (Butterfly.tens Cm : Butterfly.Op (Fin D)) xs).length)
          (h' : j < (layerH P K D S ρ hρ xs).length), ∀ c,
          ‖(prop14Proc (P := P) (S := S) hρ p (Butterfly.tens Cm : Butterfly.Op (Fin D)) xs)[j] c -
            (layerH P K D S ρ hρ xs)[j] c‖ < Real.sqrt 2 * 2⁻¹ ^ p) ∧
        IRuns Isym tbl (.call e14) (NLogN.KIL.encK st f) (NLogN.KIL.encK st (Function.update f 0 (gflat zs' ++ l))) c ∧
        (c : ℝ) ≤ C₀ * ((vol (layerShape P K D S) * r : ℕ) : ℝ) * (w + 1) *
          (D : ℝ) ^ (1 - (2 : ℝ)⁻¹ ^ 102)

end IntMul.OpenAI.R154.P.NLogN.KFV

end

-- from K_Defs29
section

set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false

namespace IntMul.OpenAI.R154.P.NLogN.KFV
open _root_.NLogN hiding posE tE twA twB vE zX
open _root_.IntMul.OpenAI.R154.P.NLogN
open _root_.NLogN.KFV hiding Cost18 EwB18 Log18Need P14Need P14Uat Par18Need cChunk total18
open _root_.IntMul.OpenAI.R154.P.NLogN.KFV

open _root_.IntMul
open _root_.NLogN.RS
open _root_.NLogN.KIL hiding Cfg FR St aE cBr cFwd cStep kG negP outR padL pre2 srcT swF yB
open _root_.NLogN.KFD
open _root_.NLogN.KFB hiding blk permL permP
open _root_.NLogN.KFH hiding gD
open _root_.AModel hiding blk hdPos
open _root_.Butterfly hiding Op

variable {Pp : ℕ} {I : List Sym} {iprog : Fin Pp → IStmt HS Pp}













section Paper

open _root_.Synth
open _root_.GlueLayout
open _root_.GlueP14 hiding blk cRec
open _root_.GlueError

variable (D ℓ K : ℕ) [NeZero D] (long : Fin D → Bool)

/-- Cost bound of a chunk round. -/
noncomputable def cChunk (W B : ℕ) (C₀ : ℝ) : ℕ :=
  cDPush B + ⌈C₀ * ((2 ^ NLogN.KFV.nB D ℓ K long * 2 ^ ℓ : ℕ) : ℝ) * (W + 1) *
    (D : ℝ) ^ (1 - (2 : ℝ)⁻¹ ^ 102)⌉₊ + 9 * (2 * B + 2)

end Paper

end IntMul.OpenAI.R154.P.NLogN.KFV

end

-- from K_Defs31
section

namespace IntMul.OpenAI.R154.P.NLogN.KFV
open _root_.NLogN hiding posE tE twA twB vE zX
open _root_.IntMul.OpenAI.R154.P.NLogN
open _root_.NLogN.KFV hiding Cost18 EwB18 Log18Need P14Need P14Uat Par18Need cChunk total18
open _root_.IntMul.OpenAI.R154.P.NLogN.KFV

open _root_.IntMul
open _root_.IntMul.OpenAI.Glue hiding KP LP dP rP αP γP ℓP
open _root_.IntMul.OpenAI.R154

/-- **The width condition of the uniform Proposition 14** for its constant `A`: the width growth
`EwB A D` fits in `p + 3` for large `n`. It holds for fixed `A` when `log_{10^6} Gb(A) < 2^75`
(`EwB ≈ Gb^2 · D^{log_{10^6} Gb}`, `D ≈ b^{2^-75}`, `p = 6b`), so it is supplied with `A`. -/
def EwB18 (A : ℕ) : Prop := ∃ n₂ : ℕ, ∀ n : ℕ, n₂ ≤ n → KFM.EwB A (IntMul.OpenAI.R154.dP n - 1) ≤ pP n + 3

/-- **The numeric side conditions of Proposition 18** (pure arithmetic of the parameters). -/
def Par18Need : Prop :=
  ∃ n₁ : ℕ, ∀ n : ℕ, IntMul.OpenAI.Glue.n0 ≤ n → n₁ ≤ n →
    let p := pP n
    let ℓ := ℓP n
    let K := KP n
    let D := IntMul.OpenAI.R154.dP n - 1
    let Zm := D * ℓ + ℓ + 8
    let Bm := p + 2 + Zm + D * ℓ + D + 1
    2 ≤ D ∧ 2 ≤ ℓ ∧ 6 ≤ K ∧ K + 1 ≤ ℓ ∧
    80 * Zm * (Zm + 2) ≤ 2 ^ K ∧
    zsz (p : ℤ) ≤ ℓ ∧
    (K : ℝ) ≤ 2 * (D : ℝ) ^ ((2 : ℝ)⁻¹ ^ 51) ∧
    2 * p + 7 < 2 ^ ℓ ∧
    2 * (2 * Zm + 4) ^ 3 + 2 ≤ 2 ^ ℓ ∧
    (K * D + 11) * (Zm + 2) ≤ 2 ^ ℓ ∧
    (∀ B ≤ Bm, 10 ^ 12 * (B + 2) ^ 3 + 16 * KFUU.cU B ≤ 2 ^ ℓ) ∧
    2 * 2 ^ (D * ℓ) * (3 * ℓ + 1) ≤ 2 ^ p ∧
    D * ℓ ≤ p

end IntMul.OpenAI.R154.P.NLogN.KFV

end

-- from K_Defs31
section

set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false

namespace IntMul.OpenAI.R154.P.NLogN.KFV
open _root_.NLogN hiding posE tE twA twB vE zX
open _root_.IntMul.OpenAI.R154.P.NLogN
open _root_.NLogN.KFV hiding Cost18 EwB18 Log18Need P14Need P14Uat Par18Need cChunk total18
open _root_.IntMul.OpenAI.R154.P.NLogN.KFV

open _root_.IntMul
open _root_.NLogN.RS
open _root_.NLogN.KIL hiding Cfg FR St aE cBr cFwd cStep kG negP outR padL pre2 srcT swF yB
open _root_.NLogN.KFD
open _root_.NLogN.KFB hiding blk permL permP
open _root_.NLogN.KFH hiding gD
open _root_.NLogN.KFC hiding dbl enc encF mvB sT
open _root_.NLogN.KFT hiding tE
open _root_.Synth
open _root_.AModel hiding blk hdPos
open _root_.AModelL12
open _root_.GlueLayout
open _root_.GlueP14 hiding blk cRec
open _root_.GlueError
open _root_.IntMul.OpenAI.Glue hiding KP LP dP rP αP γP ℓP
open _root_.IntMul.OpenAI.R154
open _root_.IntMul.OpenAI.RCost hiding Ncost c es lam' δ ε κ τ
open _root_.IntMul.OpenAI.R154

/-- `P14U` at a named constant `A`. -/
def P14Uat (A : ℕ) : Prop :=
  ∃ (nU : ℕ) (U : ∀ E : ℕ, (Fin nU → Fin (7 + E)) → Fin nU → IStmt HS (7 + E))
    (entry : Fin nU) (dS14 : Fin HS) (C₀ : ℝ),
    dS14 = 36 ∧ 0 ≤ C₀ ∧
    ∀ (E : ℕ) (ext : Fin E → IStmt HS (7 + E)) (idx : Fin nU → Fin (7 + E)),
      (∀ i, KFM.kTable ext (idx i) = U E idx i) →
      ∀ Isym : List Sym, P14Need Isym (KFM.kTable ext) (idx entry) dS14 A C₀






/-- **The exact cost of a Proposition 18 call.** -/
noncomputable def total18 (C₀ Kc : ℝ) (Cs p ℓ K : ℕ) (ts : List ℕ) [NeZero ts.length] : ℕ :=
  let D := ts.length
  let lg := long18 ℓ ts
  let n := n18 ℓ K ts
  let B := B18 p ℓ K ts
  let U := U18 ℓ K ts
  let cCh := cChunk D ℓ K lg (p + 2) B C₀
  cSet18 Cs p ℓ K ts +
    (cCore18 (cLayIn D ℓ K lg Kc n (p + 2) B + NLogN.KFV.cFwd D ℓ K lg (p + 2) B cCh U)
      (cOpp D ℓ K lg (p + 2) B cCh U + cLayOut D ℓ K lg Kc n (p + 2) B)
      n ℓ p B (BK18 p ℓ K ts) (φ18 p ℓ) + cSet18 Cs p ℓ K ts) + 2

/-- **The asymptotic cost of a Proposition 18 call** (for every choice of the constants of the
Proposition 14 call, the swap and the setup). -/
def Cost18 : Prop :=
  ∀ (C₀ Kc : ℝ) (Cs : ℕ), 0 ≤ C₀ → 0 ≤ Kc →
    ∃ (C : ℝ) (A' n₁ : ℕ), 0 ≤ C ∧ ∀ n : ℕ, IntMul.OpenAI.Glue.n0 ≤ n → n₁ ≤ n →
    ∀ (ts : List ℕ) [NeZero ts.length], ts.length + 1 = IntMul.OpenAI.R154.dP n →
      (∀ t ∈ ts, t = IntMul.OpenAI.R154.rP n ∨ 2 * t = IntMul.OpenAI.R154.rP n) →
      (total18 C₀ Kc Cs (pP n) (ℓP n) (KP n) ts : ℝ) ≤
        C * ((ts.prod * IntMul.OpenAI.R154.rP n * (pP n + 3) : ℕ) : ℝ) *
          Ncost (6 * (IntMul.lg n : ℝ)) (IntMul.OpenAI.R154.dP n) (KP n) (ℓP n) (αP n) *
          (Real.log (6 * (IntMul.lg n : ℝ)) + 1) ^ A'


end IntMul.OpenAI.R154.P.NLogN.KFV

end

-- from K_Defs31
section

namespace IntMul.OpenAI.R154.P.NLogN.KFV
open _root_.NLogN hiding posE tE twA twB vE zX
open _root_.IntMul.OpenAI.R154.P.NLogN
open _root_.NLogN.KFV hiding Cost18 EwB18 Log18Need P14Need P14Uat Par18Need cChunk total18
open _root_.IntMul.OpenAI.R154.P.NLogN.KFV

open _root_.IntMul
open _root_.IntMul.OpenAI.Glue hiding KP LP dP rP αP γP ℓP
open _root_.IntMul.OpenAI.R154

/-- **The logarithmic factor of the Kronecker products** (pure arithmetic). -/
def Log18Need : Prop :=
  ∃ (c : ℝ) (n₁ : ℕ), ∀ n : ℕ, IntMul.OpenAI.Glue.n0 ≤ n → n₁ ≤ n →
    let p := pP n
    let ℓ := ℓP n
    let m := 2 * (NLogN.KFV.kb p ℓ * 2 ^ ℓ + 2)
    (((zsz ((m + 1 : ℕ) : ℤ) + 2) * (zsz (((zsz ((m + 1 : ℕ) : ℤ) + 2) ^ 4 : ℕ) : ℤ) + 1) : ℕ) : ℝ) ≤
      c * ((ℓ : ℝ) + Real.logb 2 (6 * (IntMul.lg n : ℝ)) + 1) *
        (Real.log (6 * (IntMul.lg n : ℝ)) + 1)

end IntMul.OpenAI.R154.P.NLogN.KFV

end



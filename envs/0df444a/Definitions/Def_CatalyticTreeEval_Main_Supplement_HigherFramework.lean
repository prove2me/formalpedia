-- Prove2me | Definitions.Def_CatalyticTreeEval_Main_Supplement_HigherFramework
-- name    : CatalyticTreeEval_Main_Supplement_HigherFramework
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-15T19:34:10.416492+00:00
-- url     : https://prove2.me/theorems/cb2f2601-f35f-4af1-89c2-f36666e9ea65
-- title:
--   Definition 3.15 and Theorem 4.11 — arity-r framework and readout
-- statement:
--   For a score set $S\subseteq\mathbb Z_m$, the $r$-fold sumset and noncancellation property mean
--   $$rS=\left\{\sum_{i<r}s_i:s_i\in S\right\},\qquad \sum_{i<r}s_i=0\ \Longrightarrow\ \forall i<r,\ s_i=0.$$
--   The higher-arity framework supplies $r\ge2$, $m>1$, a positive label length, a matching family of exact size $2^\ell$, an $rS$-decoder of sparsity $k$, and a common access-space parameter $s\ge\log_2(dm)$. Uniform vector and decoder printing use the unchanged published charged interfaces with an arity-bearing header.
--
--   The packed-label encoding and decoding reuse the binary readout with zero padding to $\max(d,\lceil\ell/\lfloor\log_2m\rfloor\rceil)$. Any extra padded coordinates are initialized in charged local workspace; the theorem receives exactly $r+1$ registers of the original dimension $d$. This layer extends the binary setting without imposing binary noncancellation, a bound on $r$, or an auxiliary output-family hypothesis.
-- source:
--   Alexandra Henzinger, Edward Pyne, Seyoon Ragavan, Catalytic Tree Evaluation from Matching Vectors, STOC 2027 submission #533 (October 2026), canonical source.pdf SHA-256 17c3a71f0fb5afe2456558477e16fbac4200191e6e68f0facf212e24cb4ef238, Definition 3.15, printed p. 18 (PDF p. 20); §4 standing assumptions, printed p. 21 (PDF p. 23); Theorem 4.11, printed pp. 28–29 (PDF pp. 30–31)

import Definitions.Def_CatalyticTreeEval_Main_Supplement_HigherOracle
import Definitions.Def_CatalyticTreeEval_Main_Readout

set_option autoImplicit false

namespace CatalyticTreeEval.Main.Supplement

def rSumset {m : ℕ} (r : ℕ) (S : Set (ZMod m)) : Set (ZMod m) :=
  {a | ∃ scores : Fin r → ZMod m, (∀ i, scores i ∈ S) ∧ a = ∑ i, scores i}

def RNoncancelling {m : ℕ} (r : ℕ) (S : Set (ZMod m)) : Prop :=
  ∀ scores : Fin r → ZMod m, (∀ i, scores i ∈ S) →
    (∑ i, scores i) = 0 → ∀ i, scores i = 0

/-- Arity is an input parameter, without any upper bound relative to label length. -/
structure Frame where
  r : ℕ
  m : ℕ
  d : ℕ
  l : ℕ
  k : ℕ
  s : ℕ
  S : Set (ZMod m)
  U : Label l → Vec m d
  V : Label l → Vec m d
  D : Decoder m k

def Frame.valid (F : Frame) : Prop :=
  2 ≤ F.r ∧ 1 < F.m ∧ 0 < F.l ∧ SMatching F.S F.U F.V ∧
  RNoncancelling F.r F.S ∧ IsDecoder (rSumset F.r F.S) F.D ∧
  log₂ (F.d * F.m) ≤ F.s

def Frame.params (a : List Bool) (F : Frame) : List Bool :=
  listCode a ++ natsCode [F.r,F.m,F.d,F.l,F.k]

def Frame.access (F : Frame) (a : List Bool) (MV MD : Machine) (C : ℝ) : Prop :=
  VectorAccess MV (F.params a) F.U F.V (C * F.s) ∧
    DecoderAccess MD (F.params a) F.D (C * F.s)

/-- Zero padding only, exactly as in the binary readout. -/
def binaryFrame (F : Frame) : CatalyticTreeEval.Main.Frame :=
  ⟨F.m,F.d,F.l,F.k,F.s,F.S,F.U,F.V,F.D⟩

def paddedDimension (F : Frame) : ℕ := CatalyticTreeEval.Main.paddedDimension (binaryFrame F)

def readoutEncoding (F : Frame) (y : Label F.l) : Vec F.m (paddedDimension F) :=
  CatalyticTreeEval.Main.readoutEncoding (binaryFrame F) y

def readoutDecode (F : Frame) (v : Vec F.m (paddedDimension F)) : Label F.l :=
  CatalyticTreeEval.Main.readoutDecode (binaryFrame F) v

end CatalyticTreeEval.Main.Supplement



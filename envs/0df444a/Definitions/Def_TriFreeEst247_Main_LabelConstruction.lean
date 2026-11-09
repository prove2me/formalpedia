-- Prove2me | Definitions.Def_TriFreeEst247_Main_LabelConstruction
-- name    : TriFreeEst247_Main_LabelConstruction
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-08T10:06:44.166169+00:00
-- url     : https://prove2.me/theorems/a165ebd6-fbd5-43ba-929d-70f81524cbf8
-- title:
--   Short labels, endpoint decoding, and the local graph CSP
-- statement:
--   For $\lambda\ge0$ and $0<\eta<1/10$, put $L=\lceil2/\eta\rceil$ and $t_0=\lceil(1+\lambda)^2/\eta^2\rceil$. A label is a color and $L$ Boolean vectors of length $t_0$:
--
--   $$A_{\lambda,\eta}=[L]\times\{0,1\}^{[L]\times[t_0]}.$$
--
--   For labels $(a,\beta),(a',\beta')$, the decoder returns zero on a nonedge. On an edge it deletes precisely when $a=a'$ or $\lambda t_0^{-1}\sum_q\beta_{i,q}\beta'_{i,q}>1$, with block $i=(a+a')\bmod L$ in the zero-based convention. The decoded deletion set is $D_\sigma$. Let $w_{xy}$ be this deletion indicator and $v_{xy}$ the indicator that an input edge is retained. The local rule is
--
--   $$Q_{xyz}(a,b,c)=1-\frac{1}{1+\lambda}\left(\frac{n-1}{2n}w_{xy}(a,b)+\frac{\lambda(n-1)(n-2)}{6n^2}v_{xy}(a,b)v_{yz}(b,c)v_{zx}(c,a)\right).$$
--
--   The rule uses only $n$, the labels, and the three adjacency bits, and defines $Q_G$ without any samples or optimal solution. All labelings are allowed, with arbitrary record bits and arbitrary colors.
--
--   **Formalization Note** Colors, blocks, and record positions start at zero. Finite modular addition implements the paper's block number minus one. The parameter helpers use natural ceilings exactly; out-of-domain zero denominators follow Lean's total convention and are excluded by the statements.
-- source:
--   Asaf Shapira, Nick Kushnir, Triangle-Freeness: Estimation Is as Easy as Testing, STOC 2027 submission #247 (October 2026), source.pdf SHA-256 c24a6ad41f5c2465027e143e0aa757c3288add8cceb703078b9c0c2e18a0c3ad, p.10–11, Definitions 3.1 and 3.2

import Mathlib
import Definitions.Def_TriFreeEst247_Main_Score
import Definitions.Def_TriFreeEst247_Main_DenseCSP

noncomputable section

namespace TriFreeEst247.Main

/-- Section 3.2, p.10: exact ceilings, not asymptotic substitutes. -/
def colorCount (η : ℝ) : ℕ := ⌈2 / η⌉₊
def sampleCount (lam η : ℝ) : ℕ := ⌈(1 + lam)^2 / η^2⌉₊

abbrev Label (lam η : ℝ) :=
  Fin (colorCount η) × (Fin (colorCount η) → Fin (sampleCount lam η) → Bool)

/-- Addition in Fin L is addition modulo L: block i here is the paper's block i+1. -/
def blockIndex {L : ℕ} (a b : Fin L) : Fin L := a + b

def decode (lam η : ℝ) (edge : Bool) (a b : Label lam η) : Bool := by
  classical
  exact edge && decide (a.1 = b.1 ∨
    lam / (sampleCount lam η : ℝ) *
      (∑ q, if a.2 (blockIndex a.1 b.1) q && b.2 (blockIndex a.1 b.1) q then (1 : ℝ) else 0) > 1)

def deletedIndicator (lam η : ℝ) (e : Bool) (a b : Label lam η) : ℝ :=
  if decode lam η e a b then 1 else 0

def retainedIndicator (lam η : ℝ) (e : Bool) (a b : Label lam η) : ℝ :=
  if e && !(decode lam η e a b) then 1 else 0

/-- Definition 3.2, p.11: this rule is independent of G; only three input bits are read. -/
def localRule (lam η : ℝ) (n : ℕ) (exy eyz ezx : Bool)
    (a b c : Label lam η) : ℝ :=
  1 - (1 + lam)⁻¹ *
    (((n : ℝ) - 1) / (2 * (n : ℝ)) * deletedIndicator lam η exy a b +
      lam * ((n : ℝ) - 1) * ((n : ℝ) - 2) / (6 * (n : ℝ)^2) *
        retainedIndicator lam η exy a b * retainedIndicator lam η eyz b c *
        retainedIndicator lam η ezx c a)

def graphCSP {n : ℕ} (G : Graph n) (lam η : ℝ) : CSP n (Label lam η) :=
  fun x y z => localRule lam η n (graphOracle G (x,y))
    (graphOracle G (y,z)) (graphOracle G (z,x))

def decodedDeletion {n : ℕ} (G : Graph n) (lam η : ℝ)
    (σ : Fin n → Label lam η) : EdgeSet n := by
  classical
  exact (edges G).filter (fun e => ∃ x y, e = s(x,y) ∧ decode lam η true (σ x) (σ y) = true)

end TriFreeEst247.Main



-- Prove2me | Definitions.Def_PPSLattice_memCircuit
-- name    : PPSLattice_memCircuit
-- status  : Definition
-- author  : @iris
-- created : 2026-11-09T22:33:52.558221+00:00
-- url     : https://prove2.me/theorems/61e3bc0f-5538-4586-bc8c-fded96fbc6ff
-- title:
--   The set membership circuit $f_S$
-- statement:
--   For $N\ge1$, $k=\lceil\log N\rceil$ and $S\subseteq[N]$, the circuit $f_S$ on $k$ input bits computes
--   $$f_S(x)=\bigvee_{s\in S}\ \bigwedge_{j<k}(x_j\oplus s_j\oplus1),$$
--   $s_j$ the $j$-th bit of $\mathrm{encvec}(s)$, built as in the proof of Claim 4.10: each literal is $x_j$ or its negation (one NAND gate), the AND of the $k$ literals of each $s$ is a balanced binary tree, and so is the OR over $S$, each AND/OR gate using at most 3 NAND gates in 2 levels. For $k=0$ the empty AND is the constant $1$; for $S=\emptyset$ the output is the constant $0$.
--
--   It is the circuit used in KGen ($\mathbf A_S=\mathrm{EvalF}(\mathbf A,f_S)$) and in Decode ($\mathbf H_{S,i}$).
-- source:
--   Goyal–Yadugiri, New Results in Adaptively-Secure Broadcast Encryption and Succinct Computational Secret Sharing from Standard Lattices, STOC 2027 submission (manuscript sha256 7f9c493f…), Construction 4.6, p.21; proof of Claim 4.10, p.23

import Mathlib
import Definitions.Def_RestrictedDec_Circuit
set_option autoImplicit false

namespace PPSLattice

/-- One AND gate (`orOp = false`: `NAND(NAND(a, b), NAND(a, b))`, two NAND gates in two levels) or OR
gate (`orOp = true`: `NAND(NAND(a, a), NAND(b, b))`, three NAND gates in two levels) appended to the
gate list `gs` of a circuit on `ℓ` inputs; returns the new list and the output wire. -/
def gateOp (ell : ℕ) (orOp : Bool) (gs : List (ℕ × ℕ)) (a b : ℕ) : List (ℕ × ℕ) × ℕ :=
  let w := ell + gs.length
  if orOp then (gs ++ [(a, a), (b, b), (w, w + 1)], w + 2) else (gs ++ [(a, b), (w, w)], w + 1)

/-- One level of a binary tree: combine consecutive pairs of wires with `gateOp` (an odd last wire is
passed on). -/
def treeLevel (ell : ℕ) (orOp : Bool) : List (ℕ × ℕ) → List ℕ → List (ℕ × ℕ) × List ℕ
  | gs, a :: b :: rest =>
    let p := gateOp ell orOp gs a b
    let r := treeLevel ell orOp p.1 rest
    (r.1, p.2 :: r.2)
  | gs, ws => (gs, ws)

/-- `k` levels of a binary tree; `⌈log₂ t⌉` levels reduce `t ≥ 1` wires to one. -/
def treeReduce (ell : ℕ) (orOp : Bool) : ℕ → List (ℕ × ℕ) → List ℕ → List (ℕ × ℕ) × List ℕ
  | 0, gs, ws => (gs, ws)
  | k + 1, gs, ws =>
    let p := treeLevel ell orOp gs ws
    treeReduce ell orOp k p.1 p.2

/-- The **set membership circuit** `f_S` on `k = ⌈log₂ N⌉` input bits,
`f_S(x) = ⋁_{s∈S} ⋀_{j<k} (x_j ⊕ s_j ⊕ 1)` with `s_j` the `j`-th bit of `encvec(s)`, built as in the proof of
Claim 4.10: each literal is `x_j` (if `s_j = 1`) or its negation `NAND(x_j, x_j)` (if `s_j = 0`); the AND
of the `k` literals of each `s` (taken in increasing order) is a binary tree of depth `⌈log k⌉` of AND
gates, and the OR over `S` a binary tree of depth `⌈log |S|⌉` of OR gates, each AND/OR gate being made of
at most 3 NAND gates in 2 levels. For `k = 0` the empty AND is the constant `1` (one NAND gate of a
constant wire), and for `S = ∅` the output is the constant `0`.
Goyal–Yadugiri, *New Results in Adaptively-Secure Broadcast Encryption and Succinct Computational Secret Sharing from Standard Lattices*, STOC 2027 submission (manuscript sha256 7f9c493f…), Construction 4.6, KGen Step 1, p.21 ("consider the circuit f_S where f_S(x) = 1 if x ∈ S and 0
otherwise"); proof of Claim 4.10, p.23 ("We write f_S(x) = ⋁_{s∈S} ⋀_{j∈[⌈log N⌉]}(x_j ⊕ s_j ⊕ 1) …").

**Formalization Note.** Input bit `j` is bit `j` (least significant first) of `encvec(i)`, the code of
`i − 1`; so `f_S(encvec(i)) = [i ∈ S]` for `i ∈ [N]`. Constant wires are wires that do not exist yet,
which `RestrictedDec.Circuit.eval` reads as `0`. -/
def memCircuit (N : ℕ) (S : Finset ℕ) : RestrictedDec.Circuit :=
  let k := Nat.clog 2 N
  let step : List (ℕ × ℕ) × List ℕ → ℕ → List (ℕ × ℕ) × List ℕ := fun acc s =>
    let lit := (List.range k).foldl (fun (p : List (ℕ × ℕ) × List ℕ) j =>
        if (s - 1).testBit j then (p.1, p.2 ++ [j])
        else (p.1 ++ [(j, j)], p.2 ++ [k + p.1.length])) (acc.1, [])
    let r : List (ℕ × ℕ) × ℕ :=
      if k = 0 then (lit.1 ++ [(k + lit.1.length, k + lit.1.length)], k + lit.1.length)
      else
        let t := treeReduce k false (Nat.clog 2 k) lit.1 lit.2
        (t.1, t.2.headD 0)
    (r.1, acc.2 ++ [r.2])
  let perS := (S.sort (· ≤ ·)).foldl step ([], [])
  if S = ∅ then { gates := perS.1, outs := [k + perS.1.length] }
  else
    let t := treeReduce k true (Nat.clog 2 S.card) perS.1 perS.2
    { gates := t.1, outs := [t.2.headD 0] }

end PPSLattice



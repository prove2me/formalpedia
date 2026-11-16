-- Prove2me | Definitions.Def_UniformADProbes_Trace_Supplement_cyclic_construction
-- name    : UniformADProbes_Trace_Supplement_cyclic_construction
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-15T17:19:38.707221+00:00
-- url     : https://prove2.me/theorems/0395dad3-9386-4b87-bd0b-267f270e2cc1
-- title:
--   Appendix A.2 — Charged original-order cyclic-matrix constructor
-- statement:
--   For each positive integer $N$, this deterministic constructor emits the Appendix A cyclic matrix using only the published instructions: identity, the two matrix inputs, addition, multiplication, and scaling by an integer. It returns identity at $N=1$. For $N\ge2$ it computes the exact condensation constants by charged binary arithmetic, constructs $Z_i$ by Horner sums, and sets $J=J_N$.
--
--   The Gram-entry registers are $B_{rs}=JZ_r^*Z_sJ$. For each $k\ge1$, Bird's homogeneous recurrence starts at $F_1=G$, uses $F_{q+1}=\mu(F_q)G$, and returns $(-1)^{k-1}(F_k)_{00}$. Here $\mu$ keeps strictly upper entries, is zero below the diagonal, and has diagonal entry $-\sum_{\ell>i}F_{\ell\ell}$. Apply it to the leading $k$ Gram array and to its column replacements to obtain $\widehat\Delta_k,\widehat\Delta_{k,i}$. The emitted residuals and output are
--   $$
--   V_0=J,\qquad V_k=Z_k\widehat\Delta_k-\sum_{i<k}Z_i\widehat\Delta_{k,i},\qquad
--   C_N=V_0V_0^*+\sum_{k=0}^{N-2}(V_k+V_{k+1})(V_k+V_{k+1})^*.
--   $$
--   Every array stores references to matrices of the original input order. Neither determinant nor adjugate is a primitive circuit instruction; Bird's recurrence expands them into permitted operations. Adjoint registers reverse multiplication order. The constructor never reads a tree, a rank, or a trace.
--
--   **Formalization Note** Schoolbook arithmetic charges come from the published binary operations and builder. Table access, copying and append operations also pay binary index-copy costs. Factorial, powers of two, $R$, $H_0$, $H_1$ and $\tau$ are computed with these charges. Theorem A.2, rather than this definition, asserts validity, formal sum-of-squares status, degree and polynomial resource bounds.
-- source:
--   Zhipeng Lu, Uniform adjacency-degree probes from differential rigidity, STOC 2027 submission #25 (October 2026), Appendix A.1–A.2, equations (13), (16)–(17), p. 11–14 (PDF p. 12–15); https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/25.pdf

import Definitions.Def_UniformADProbes_Trace_circuits
import Definitions.Def_UniformADProbes_Trace_Supplement_rank_condensation

set_option autoImplicit false

namespace UniformADProbes.Trace.Supplement

/-- Factorial, computed by charged binary multiplication. -/
def binaryFactorial : ℕ → Charged ℕ
  | 0 => ⟨1, 1⟩
  | n + 1 =>
    let f := binaryFactorial n
    let m := binaryMul f.value (n + 1)
    ⟨m.value, f.cost + m.cost + 4 * refBits (n + 1) + 4⟩

/-- The exact constants of A.1, with their binary construction costs. -/
def chargedTau (N : ℕ) : Charged ℕ :=
  let n1 := binaryAdd N 1
  let mm := binaryMul N n1.value
  let M := mm.value / 2
  let n2 := binaryMul N N
  let n3 := binaryMul n2.value N
  let l := binaryMul 3 n3.value
  let r := binaryPower l.value (N - 1)
  let e := binaryMul (N - 2) (M - 2)
  let p := binaryPower 2 e.value
  let h := binaryMul (M - 1) r.value
  let h0 := binaryMul h.value p.value
  let hpow := binaryPower h0.value (N - 1)
  let f := binaryFactorial N
  let h1 := binaryMul f.value hpow.value
  let tau := binaryAdd h1.value 2
  ⟨tau.value, n1.cost + mm.cost + n2.cost + n3.cost + l.cost + r.cost + e.cost +
    p.cost + h.cost + h0.cost + hpow.cost + f.cost + h1.cost + tau.cost +
    100 * (1 + refBits N + refBits M)^2⟩

/-- Copying a table, including every stored index, is charged. -/
def copyRefs (a : Array DualRef) : Emit Unit :=
  charge (a.foldl (fun c r => c + refBits r.1 + refBits r.2 + 1) 1)

def pushRef (a : Array DualRef) (v : DualRef) : Emit (Array DualRef) := do
  copyRefs a
  charge (refBits v.1 + refBits v.2)
  return a.push v

/-- Z_0=I, followed by Horner sums over U_1,...,U_{M-1}, excluding U_0. -/
def emitCondensed (N : ℕ) (i z : DualRef) (U : Array DualRef) :
    Emit (Array DualRef) := do
  let tau := chargedTau N
  charge tau.cost
  let mut Z := #[i]
  for j in List.range (N - 1) do
    let pow := binaryPower 2 j
    let t := binaryMul pow.value tau.value
    charge (pow.cost + t.cost + refBits j + refBits N)
    let base ← dualScale (t.value : ℤ) i
    let mut acc := z
    for a in (List.range (U.size - 1)).reverse do
      let u ← tableGet U (a + 1) z
      acc ← dualAdd u (← dualMul base acc)
    Z ← pushRef Z acc
  return Z

/-- Flat arrays index original-order registers; no enlarged matrix is evaluated. -/
def gridGet (a : Array DualRef) (k r s : ℕ) (z : DualRef) : Emit DualRef := do
  let pos := binaryMul r k
  let ix := binaryAdd pos.value s
  charge (pos.cost + ix.cost)
  tableGet a ix.value z

/-- Bird's mu: upper entries retained, lower entries zero, diagonal negative
sum of the entries strictly below it ON THE DIAGONAL. -/
def emitMu (k : ℕ) (F : Array DualRef) (z : DualRef) : Emit (Array DualRef) := do
  let mut result := #[]
  for r in List.range k do
    for s in List.range k do
      charge (10 * (1 + refBits r + refBits s + refBits k)^2)
      let v ← if r < s then gridGet F k r s z else if s < r then pure z else do
        let mut acc := z
        for l in List.range k do
          if r < l then acc ← dualAdd acc (← gridGet F k l l z)
        dualScale (-1) acc
      result ← pushRef result v
  return result

/-- Shared ordinary multiplication of arrays of references. -/
def emitGridMul (k : ℕ) (F G : Array DualRef) (z : DualRef) :
    Emit (Array DualRef) := do
  let mut result := #[]
  for r in List.range k do
    for s in List.range k do
      let mut acc := z
      for l in List.range k do
        charge (10 * (1 + refBits k + refBits r + refBits s + refBits l)^2)
        let a ← gridGet F k r l z
        let b ← gridGet G k l s z
        acc ← dualAdd acc (← dualMul a b)
      result ← pushRef result acc
  return result

/-- Positive homogeneous Bird determinant circuit; never introduces an identity
for the Gram-entry algebra. Used only at k>=1. -/
def emitBird (k : ℕ) (G : Array DualRef) (z : DualRef) : Emit DualRef := do
  copyRefs G
  let mut F := G
  for q in List.range (k - 1) do
    charge (refBits q + refBits k)
    F ← emitGridMul k (← emitMu k F z) G z
  let d ← gridGet F k 0 0 z
  dualScale (if (k - 1) % 2 = 0 then 1 else -1) d

/-- G_k, or G_k with column c replaced by (g_{i,k})_{i<k}; entries
are J Z_r* Z_s J. The optional column is construction data, never an oracle. -/
def emitGram (k : ℕ) (c : Option ℕ) (Z : Array DualRef)
    (J z : DualRef) : Emit (Array DualRef) := do
  let mut G := #[]
  for r in List.range k do
    for s in List.range k do
      charge (10 * (1 + refBits k + refBits r + refBits s)^2)
      let a ← tableGet Z r z
      let b ← tableGet Z (if c = some s then k else s) z
      let v ← dualMul (← dualMul (← dualMul J (dualSwap a)) b) J
      G ← pushRef G v
  return G

/-- Equations (16)-(17), with a shared probe family, no rank tests and no
scalar determinant, inverse, trace, or adjugate instruction. -/
def cyclicProgram (N : ℕ) : ℕ × Builder :=
  (do
    if N ≤ 1 then return (← emit .identity)
    let (i,a,d,z) ← initial
    let U ← emitProbes N i a d z
    let J ← emitDistance N i a d
    let Z ← emitCondensed N i z U
    let mut V := #[J]
    for h in List.range (N - 1) do
      let k := h + 1
      let delta ← emitBird k (← emitGram k none Z J z) z
      let zk ← tableGet Z k z
      let mut vk ← dualMul zk delta
      for c in List.range k do
        let dc ← emitBird k (← emitGram k (some c) Z J z) z
        let zc ← tableGet Z c z
        vk ← dualAdd vk (← dualScale (-1) (← dualMul zc dc))
      V ← pushRef V vk
    let mut out ← dualMul J (dualSwap J)
    for k in List.range (N - 1) do
      let v ← dualAdd (← tableGet V k z) (← tableGet V (k + 1) z)
      out ← dualAdd out (← dualMul v (dualSwap v))
    return out.1).run {}

def cyclicCircuit (N : ℕ) : Circuit :=
  let p := cyclicProgram N
  ⟨p.2.code, p.1⟩

def cyclicCost (N : ℕ) : ℕ := (cyclicProgram N).2.cost

end UniformADProbes.Trace.Supplement



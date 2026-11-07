-- Prove2me | Definitions.Def_TimeSpaceMA_chunkConstraint
-- name    : TimeSpaceMA_chunkConstraint
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T10:56:54.49224+00:00
-- url     : https://prove2.me/theorems/e656d9e4-7161-49fe-a8c4-151a49e01b57
-- title:
--   Chunk constraint $E(v,c,c')$ and the record of a run
-- statement:
--   A chunk vector is $v=(z^1,r^1,c^1,\dots,z^B,r^B,c^B)$ with $z^k\in\mathbb Z^g$, $r^k\in\mathbb Z^{2H}$, $c^k\in\mathbb Z^H$, of dimension $d=B(g+3H)$, and $y=(v,1,c,c')$.
--
--   Each wire of step $k$ is a linear form in $y$: a configuration input of step $1$ is a coordinate of $c$, a configuration input of a later step is an output gate of the previous step, the read bit is $\beta^k=\sum_a r^k_{(a,1)}$, and a gate is a coordinate of $z^k$.
--
--   The **chunk constraint** $E(v,c,c')$ is the sum of (i) $\gamma(w_1,w_2,z)$ for each step and each gate, (ii) $\Lambda(r^k,c^k)$ for each step, (iii) the address ties
--   $$\sum_i\Bigl(\rho_i^k-\sum_{a,o}\mathrm{bit}_i(a)r^k_{(a,o)}\Bigr)^2+\sum_i\Bigl(\chi_i^k-\sum_b\mathrm{bit}_i(b)c^k_b\Bigr)^2,$$
--   and (iv) the end ties $\sum_{i\in[S]}(z^B_{\mathrm{out}(i)}-c_i')^2$.
--
--   The **record** of the run of $B$ steps from $c$ is the $0/1$ chunk vector of its gate values, with $r^k$ the unit vector at $(a_k,X_{a_kb_k})$ and $c^k$ the unit vector at $b_k$.
-- source:
--   Williams, Xi, Short Non-Interactive Proofs for Time-Space Computations, STOC 2027 submission (manuscript sha256 184c2f95…), Definition 3.7, p.10; §3.2, pp.8–9

import Definitions.Def_TimeSpaceMA_lambdaForm
import Definitions.Def_TimeSpaceMA_TransitionCircuit

namespace TimeSpaceMA

/-- Coordinates of a chunk vector `v = (z¹, r¹, c¹, …, z^B, r^B, c^B)`; p.8. The type has
`d = B(g + 3H)` elements. -/
abbrev ChunkIndex (B g H : ℕ) := Fin B × (Fin g ⊕ (Fin H × Bool) ⊕ Fin H)

/-- Coordinates of `y = (v, 1, c, c′)`; `d + 2S + 1` of them. -/
abbrev ChunkInput (S B g H : ℕ) := ChunkIndex B g H ⊕ (Unit ⊕ (Fin S ⊕ Fin S))

/-- The vector `y = (v, 1, c, c′)`; p.8. -/
def chunkY {S B g H : ℕ} (v : ChunkIndex B g H → ℤ) (c c' : Fin S → Bool) :
    ChunkInput S B g H → ℤ :=
  Sum.elim v (Sum.elim (fun _ => 1)
    (Sum.elim (fun i => ((c i).toNat : ℤ)) (fun i => ((c' i).toNat : ℤ))))

/-- The `i`-th bit of an integer in `[H]` as an integer; p.9. -/
def bitOf {H : ℕ} (i : ℕ) (a : Fin H) : ℤ := if a.val.testBit i then 1 else 0

variable {S g lg B : ℕ}

/-- The linear form of a wire at step `k` (0-based; the page's step `k + 1`), pp.8–9: configuration
inputs of the first step are the coordinates of `c`, those of a later step are the output gates of the
previous step; the read-bit input is `β^k = Σ_a r^k_{(a,1)}`; a gate is a coordinate of `z^k`. -/
def chunkWireForm (C : TransitionCircuit S g lg) (v : ChunkIndex B g (2 ^ lg) → ℤ)
    (c : Fin S → Bool) (k : Fin B) : Wire S g → ℤ
  | .config i =>
      if k.val = 0 then ((c i).toNat : ℤ)
      else v (⟨k.val - 1, by omega⟩, .inl (C.out i))
  | .read => ∑ a : Fin (2 ^ lg), v (k, .inr (.inl (a, true)))
  | .gate j => v (k, .inl j)

/-- The chunk constraint `E(v, c, c′)` (Williams, Xi, STOC 2027 submission, manuscript sha256
184c2f95…, Definition 3.7, p.10): (i) `γ` of every gate at every step; (ii) `Λ(r^k, c^k)`; (iii) the
address ties; (iv) the end ties `Σ_i (z^B_{out(i)} − c′_i)²`, which sit at the last step. -/
def chunkConstraint (C : TransitionCircuit S g lg) (X : Fin (2 ^ lg) → Fin (2 ^ lg) → Bool)
    (v : ChunkIndex B g (2 ^ lg) → ℤ) (c c' : Fin S → Bool) : ℤ :=
  ∑ k : Fin B,
    ((∑ j : Fin g, gammaForm (chunkWireForm C v c k (C.in₁ j)) (chunkWireForm C v c k (C.in₂ j))
        (v (k, .inl j))) +
      lambdaForm X (fun p => v (k, .inr (.inl p))) (fun b => v (k, .inr (.inr b))) +
      (∑ i : Fin lg, (chunkWireForm C v c k (.config (C.rowWire i)) -
        ∑ p : Fin (2 ^ lg) × Bool, bitOf i.val p.1 * v (k, .inr (.inl p))) ^ 2) +
      (∑ i : Fin lg, (chunkWireForm C v c k (.config (C.colWire i)) -
        ∑ b : Fin (2 ^ lg), bitOf i.val b * v (k, .inr (.inr b))) ^ 2) +
      (if k.val + 1 = B then
        ∑ i : Fin S, (v (k, .inl (C.out i)) - ((c' i).toNat : ℤ)) ^ 2
       else 0))

/-- The record of the run of `B` steps from `c`, a `0/1` chunk vector; p.8: `z^k` lists the gate
values of step `k`, `r^k` is the unit vector at `(a_k, X_{a_k b_k})`, and `c^k` the unit vector at
`b_k`. -/
def chunkRecord (C : TransitionCircuit S g lg) (X : Fin (2 ^ lg) → Fin (2 ^ lg) → Bool)
    (c : Fin S → Bool) : ChunkIndex B g (2 ^ lg) → ℤ := fun idx =>
  let prev := C.runConfig X c idx.1.val
  let a := (C.readAddress prev).1
  let b := (C.readAddress prev).2
  match idx.2 with
  | .inl j => ((C.gateValues prev (X a b) j).toNat : ℤ)
  | .inr (.inl p) => if p = (a, X a b) then 1 else 0
  | .inr (.inr b') => if b' = b then 1 else 0

end TimeSpaceMA



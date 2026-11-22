-- Prove2me | Definitions.Def_K230_codes
-- name    : K230_codes
-- status  : Definition
-- author  : @LG
-- created : 2026-11-21T21:13:19.867876+00:00
-- url     : https://prove2.me/theorems/69642d1b-640d-4c95-b41e-6f92b00e0fac
-- title:
--   K230: numerical formula codes
-- statement:
--   The dual Cantor pairing $P(a,b)=\mathrm{tri}(a+b)+b$ and its inverse `unP`, the numerical formula constructors `wim` (implication), `wel` (membership), `wal` (universal), `weq` (equality), `wex` (existential), the falsity code $F=1$, and the frozen K230 source bundle `bundle230`/`gated230` together with the logical row codes `rho1`–`rho8`. Ports `KCode230.v` and `Codes230.v`.
-- source:
--   https://github.com/elliotglazer/k230-rocq/blob/main/coq/settheory/KCode230.v

namespace K230
def tri : Nat → Nat | 0 => 0 | n + 1 => (n + 1) + tri n
def P (a b : Nat) : Nat := tri (a + b) + b
def unPStep : Nat × Nat → Nat × Nat | (a + 1, b) => (a, b + 1) | (0, b) => (b + 1, 0)
def unP : Nat → Nat × Nat | 0 => (0, 0) | z + 1 => unPStep (unP z)
def wim (a b : Nat) : Nat := 4 * P a b
def wel (i j : Nat) : Nat := 4 * P i j + 1
def wal (i a : Nat) : Nat := 4 * P i a + 2
def weq (i j : Nat) : Nat := 4 * P i j + 3
def F : Nat := 1
def wn (a : Nat) : Nat := wim a F
def wa (a b : Nat) : Nat := wn (wim a (wn b))
def wex (x a : Nat) : Nat := wn (wal x (wn a))
def ksubset (a b k : Nat) : Nat := wal k (wim (wel k a) (wel k b))
def krequest (b k m : Nat) : Nat := wal b (wim m (wex b (wa m (wel b k))))
def kcore (a b k m : Nat) : Nat :=
  wex k (wa (wim m (wel b k)) (wal b (wim (wel b k) (wex a (wa m (wal a (wim (ksubset a b k) (krequest b k m))))))))
def k230 (a b c : Nat) : Nat := kcore a b c c
def vacuity230 (a b c : Nat) : Nat := wa (wim (wel a b) (wal c (wel a b))) (wim (weq a b) (wal c (weq a b)))
def bundle230 (a b c : Nat) : Nat := wa (k230 a b c) (vacuity230 a b c)
def gated230 (a b c : Nat) : Nat := if c = a ∨ c = b then 0 else bundle230 a b c
def rho8 (a b c u : Nat) : Nat := wim (wim (wim c u) a) (wim (wim a c) (wim b c))
def rho7 (a b c : Nat) : Nat := wim (weq c a) (wim (weq c b) (weq a b))
def rho6 (a b : Nat) : Nat := wim (wex a (wal a b)) b
def rho5 (a b c : Nat) : Nat := wim (weq c a) (wim (wel c b) (wel a b))
def rho4 (a b c : Nat) : Nat := wim (wal a (wal b c)) (wal b (wal a c))
def rho3 (a b c : Nat) : Nat := wim (weq a b) (wim (wel c a) (wel c b))
def rho2 (a b c : Nat) : Nat := wim (wal a (wim b c)) (wim (wal a b) (wal a c))
def rho1 (a b : Nat) : Nat := wex a (weq a b)
end K230


